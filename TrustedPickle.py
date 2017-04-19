# TrustedPickle - http://trustedpickle.sourceforge.net/
# Copyright (c) 2003, Gre7g Luterman <gre7g@wolfhome.com>
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#
# * Redistributions of source code must retain the above copyright notice, this
#   list of conditions and the following disclaimer.
#
# * Redistributions in binary form must reproduce the above copyright notice,
#   this list of conditions and the following disclaimer in the documentation
#   and/or other materials provided with the distribution.
#
# * Neither the name of the Gre7g Luterman nor the names of its contributors may
#   be used to endorse or promote products derived from this software without
#   specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE
# FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
# OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

"""TrustedPickle.py contains a variety of classes and functions used to sign
pickle files with private keys.  These pickle files contain not only UNENCRYPTED
data, they also contain signatures and trust relationships which allow a program
to decide whether the data should be trusted BEFORE unpickling.

Although a two-part keying system is used to sign the data, the data itself is
intentionally unencrypted.  This is done for three important reasons:

  1. Certain governments have created laws which control the use of strong
     encryption.  Although this program uses a similar technology to verify
     who authored a file, the data is not encrypted, so that this technology
     may be exported freely.

  2. This project is not "about" data encryption, it is for creating freely-
     transferrable files whose authorship can be validated before use.

  3. By leaving the data unencrypted, the end user may retain control over
     whether the data is used or not.  The user can be informed that the file
     was not created by a trusted party (such as the original program's author)
     and given the chance to accept or reject the file before it is unpickled.

Using TrustedPickle.py has one other big advantage over blindly using regular
pickle files.  The Python maintainers stress that it may be possible to
maliciously construct a pickle file so that it executes arbitrary code.  By only
allowing your program to use data signed by yourself or one of your trusted
agents, you can reduce the risk of a third party circumventing your program's
security measures by creating such data files.

Constants available in this module:

TRUSTED:     indicates data signed with a trusted key
TRANSFERRED: indicates data with a trust relationship to a trusted key
UNKNOWN:     indicates no trust relationship links data to a trusted key
REVOKED:     indicates data signed with a revoked key

Custom exceptions thrown by this module:

FileFormatError: unexpected file end or invalid file signature encountered
MismatchedKeys:  thrown when mismatched public and private keys are used

Common classes and functions in this module:

PrivateKey:    required to sign a file or establish a trust relationship
PublicKey:     includes a signed name and e-mail address, identifying the author
Signature:     shows a programmers faith in a document
TrustRelationship:
               includes a truster, a trustee, and a transferrable flag
PublicKeyFile: file holding public keys and trust relationships
TPickle:       signed data file
NewKeys():     interactively create a public and private key pair
ModuleObject:  module wrapper

Low-level functions in this module you should not need to call:

Hash(): used in signing a string

import cPickle
import getpass
import glob
import md5
import os
import random
import re
import sets
from types import *
import zlib

# Constant
TRUSTED     = 0
TRANSFERRED = 1
UNKNOWN     = 2
REVOKED     = 3

MAGIC_ZIP   = "TrPZ"
MAGIC_UNZIP = "TrPU"
MAGIC_PRIV  = "TrPv"
MAGIC_PUB   = "TrPb"

EXT_SEARCH  = re.compile(r"(\.[^\.]+)$")

# Global
# GenSeed5x52 must be set externally if a key pair before key pair generation!
GenSeed5x52   = []  # Should be set to a list of five random longs of 52 bits.
CompressLevel = 9

class FileFormatError(Exception):
  pass
class MismatchedKeys(Exception):
  pass

def GCD(a, b):
  "Returns the greatest common denomenator of a & b"
  if a < b: a, b = b, a
  while b: a, b = b, a % b
  return a

def Solve(m, Key, n):
  "Returns (m ** Key) mod n"
  i, j = m, 1
  while Key:
    if Key & 1: j = (j * i) % n
    i = (i * i) % n
    Key >>= 1
  return j

def ExtEuclid(e, phi):
  "Returns Key, such that ((Key * e) mod phi) = 1. NOTE: Key may be negative!"
  x1, Key, y1, y2 = 0L, 1L, 1L, 0L
  while phi:
    q = e / phi
    e, phi = phi, e - (q * phi)
    x1, Key = Key - (q * x1), x1
    y1, y2 = y2 - (q * y1), y1
  return Key

def TestPrime(n):
  "Uses Fermat's little theorem to test if n is PROBABLY a prime."
  a = random.randint(2, n - 1)
  return Solve(a, n - 1, n) == 1

def Reseed():
  "Pick five new random numbers using the old ones as seeds."
  global GenSeed5x52
  for a in range(5):
    random.seed(GenSeed5x52[a])
    GenSeed5x52[a] = long(random.randint(0, 1L << 52))

def PickNums():
  "Returns three random numbers for p, q, and Key from GenSeed5x52 bits."
  #                  5         4         3         2         1
  #                 1098765432109876543210987654321098765432109876543210
  # GenSeed5x52[0]: aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  # GenSeed5x52[1]: aaaaaaaaaaaabbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
  # GenSeed5x52[2]: bbbbbbbbbbbbbbbbbbbbbbbbcccccccccccccccccccccccccccc
  # GenSeed5x52[3]: cccccccccccccccccccccccccccccccccccccccccccccccccccc
  # GenSeed5x52[4]: ccccccccccccccccccccccccccccccccccccccccccccccccxxxx
  # p = 1 + 64 a's
  # q = 1 + 64 b's
  # Key = 128 c's
  p = (1L << 64) | (GenSeed5x52[0] << 12) | (GenSeed5x52[1] >> 40)
  q = (1L << 64) | ((GenSeed5x52[1] & ((1L << 40) - 1)) << 24) | \
    (GenSeed5x52[2] >> 28)
  Key = ((GenSeed5x52[2] & ((1L << 28) - 1)) << 100) | \
    (GenSeed5x52[3] << 48) | (GenSeed5x52[4] >> 4)
  return p, q, Key

def WriteN(File, N, Bytes):
  S = ""
  for i in range(Bytes):
    S += chr(N & 0xFF)
    N >>= 8
  File.write(S)

def ReadN(File, Bytes):
  S = File.read(Bytes)
  if len(S) != Bytes: raise FileFormatError
  RetVal = 0L
  for i in range(Bytes):
    RetVal |= long(ord(S[i])) << (i << 3)
  return RetVal

def WriteS(File, Str):
  WriteN(File, len(Str), 6)
  File.write(Str)

def ReadS(File):
  L = ReadN(File, 6)
  RetVal = File.read(L)
  if len(RetVal) != L: raise FileFormatError
  return RetVal

def Hash(String):
  "Returns a 128 bit digest of the string as a long."
  return long(md5.md5(String).hexdigest(), 16)

class PrivateKey:
  """Holds a private key, used in signing documents and trust relationships.

To create a private key, instantiate the object with a filename (and optionally
a password to keep the key secure) and then pass it into the GenKeys() function,
below.  GenKeys() takes care of writing the key to disk.

To read in an existing key, instantiate with filename (and password, if one was
used in its creation), and call the Read() function.  Call the Test() function
to verify that the password used was correct.  If incorrect, use SetPassword(),
Read(), and Test() to try again.

The password on an existing private key may be changed by calling SetPassword()
and Write().  Make sure the key was decoded correctly by calling Test() BEFORE
changing the password!"""

  TestHash = Hash("Test is a test string used to validate private keys.")

  def __init__(self, Filename, Password="", Key=None):
    "Constructor."
    self.Key, self.Filename, self.Password = Key, Filename, Hash(Password)

  def SetPassword(self, Password=""):
    "Set/change a password on the private key file to make it more private."
    self.Password = Hash(Password)

  def Write(self):
    "Write key to file."
    F = open(self.Filename, "wb")
    try:
      F.write(MAGIC_PRIV)
      WriteN(F, self.Key ^ self.Password, 17)
    finally:
      F.close()

  def Read(self):
    "Read and decode the key from a file."
    F = open(self.Filename, "rb")
    try:
      if F.read(4) != MAGIC_PRIV: raise FileFormatError
      self.Key = ReadN(F, 17) ^ self.Password
    finally:
      F.close()

  def Test(self, Public):
    """Test the private key against the public key to make sure it was decoded
correctly."""
    Encode = Solve(self.TestHash, self.Key, Public.n)
    return self.TestHash == Solve(Encode, Public.Key, Public.n)

class PublicKey:
  """PublicKey is a user's public key, name, and address, signed with their
private key.  Before trusting the name or address portion of this class, be sure
to test the signature with the Test() function."""

  def __init__(self, n, Key, Name, Address, PrivVal):
    "Constructor."
    # DO NOT SAVE A REFERENCE TO THE USER'S PRIVATE KEY!!!
    self.n, self.Key, self.Name, self.Address = n, Key, Name, Address
    if isinstance(PrivVal, PrivateKey):
      H = Hash(self.Name + self.Address)
      self.Validator = Solve(H, PrivVal.Key, self.n)
    else:
      self.Validator = PrivVal

  def Write(self, File):
    "Writes PublicKey to the file."
    WriteN(File, self.n, 17)
    WriteN(File, self.Key, 16)
    WriteS(File, self.Name)
    WriteS(File, self.Address)
    WriteN(File, self.Validator, 17)

  def Read(File):
    "Static method: Returns a PublicKey read from the file."
    return PublicKey(ReadN(File, 17), ReadN(File, 16), ReadS(File), ReadS(File),
      ReadN(File, 17))
  Read = staticmethod(Read)

  def Test(self):
    """Test the Name and Address against the public key to make sure it has not
been altered."""
    H = Hash(self.Name + self.Address)
    return H == Solve(self.Validator, self.Key, self.n)

class Signature:
  """Signature is a user's vouchure for the data's integrity.  Before trusting
this signature, be sure to test it with the Test() function."""

  def __init__(self, *Args):
    "Constructors."
    if len(Args) == 2:
      self._Loaded_(*Args)
    else:
      self._New_(*Args)
  def _Loaded_(self, Signer, Validator):
    self.Signer, self.Validator = Signer, Validator
  def _New_(self, Data, PublicFile, Private):
    # DO NOT SAVE A REFERENCE TO THE USER'S PRIVATE KEY!!!
    if not Private.Test(PublicFile.MyPublicKey()): raise MismatchedKeys
    self.Signer = PublicFile.Owner
    self.Validator = Solve(Hash(Data), Private.Key, PublicFile.MyPublicKey().n)

  def Write(self, File):
    "Writes PublicKey to the file."
    WriteN(File, self.Signer, 17)
    WriteN(File, self.Validator, 17)

  def Read(File):
    "Static method: Returns a Signature read from the file."
    return Signature(ReadN(File, 17), ReadN(File, 17))
  Read = staticmethod(Read)

  def Test(self, Data, Public):
    "Test the signature."
    return Hash(Data) == Solve(self.Validator, Public.Key, Public.n)

class TrustRelationship:
  """TrustRelationship tracks a truster who trusts a trustee.  The Transferrable
flag (Y/N) indicates whether the truster trusts the trustee enough to chain on
their own trust relationships.  Before trusting the listed relationship, be sure
to test the signature with the Test() function."""

  def __init__(self, *Args):
    "Constructors."
    if len(Args) == 5:
      self._Loaded_(*Args)
    else:
      self._New_(*Args)
  def _Loaded_(self, Truster, Trustee, n, Transferrable, Validator):
    self.Truster, self.Trustee, self.n = Truster, Trustee, n
    self.Transferrable, self.Validator = Transferrable, Validator
  def _New_(self, Truster, Trustee, PrivVal, Transferrable="N"):
    # DO NOT SAVE A REFERENCE TO THE USER'S PRIVATE KEY!!!
    self.Truster, self.Trustee, self.n = Truster.Key, Trustee.Key, Truster.n
    self.Transferrable = Transferrable
    H = Hash(hex(Trustee.Key) + Transferrable)
    if isinstance(PrivVal, PrivateKey):
      self.Validator = Solve(H, PrivVal.Key, self.n)
    else:
      self.Validator = PrivVal
    if H != Solve(self.Validator, self.Truster, self.n): raise MismatchedKeys

  def Test(self):
    """Test the trustee and transferred flag against the truster's public key
to make sure it has not been altered."""
    H = Hash(hex(self.Trustee) + self.Transferrable)
    return H == Solve(self.Validator, self.Truster, self.n)

  def Write(self, File):
    "Writes TrustRelationship to the file."
    WriteN(File, self.Truster, 16)
    WriteN(File, self.Trustee, 16)
    WriteN(File, self.n, 17)
    File.write(self.Transferrable)
    WriteN(File, self.Validator, 17)

  def Read(File):
    "Static method: Returns a TrustRelationship read from the file."
    Truster, Trustee, n = ReadN(File, 16), ReadN(File, 16), ReadN(File, 17)
    Transferrable, Validator = File.read(1), ReadN(File, 17)
    return TrustRelationship(Truster, Trustee, n, Transferrable, Validator)
  Read = staticmethod(Read)

def GenKeys(PrivateFilename, Name, Address, PrivatePassword=""):
  "Generates a private and public key.  Saves private.  Set GenSeed5x52 first!"
  while True:
    # Pick valid-looking values for p, q, and PubKey
    p, q, PubKey = PickNums()
    while True:
      # Reject non-prime p
      if TestPrime(p): break
      Reseed()
      p, x, x = PickNums()
    while True:
      # Reject non-prime q
      if TestPrime(q): break
      Reseed()
      x, q, x = PickNums()
    # Calculate n and phi
    n = p * q
    phi = (p - 1) * (q - 1)
    while True:
      # Make sure PubKey and phi are mostly prime
      if (PubKey > 1) and (PubKey < phi) and (GCD(PubKey, phi) == 1): break
      Reseed()
      x, x, PubKey = PickNums()
    # Calculate PrivKey
    PrivKey = ExtEuclid(PubKey, phi)
    if PrivKey < 0: PrivKey += phi

    # Test with a random message
    M = long(random.randint(0, n))
    if Solve(Solve(M, PubKey, n), PrivKey, n) == M: break
  Private = PrivateKey(PrivateFilename, PrivatePassword, PrivKey)
  Private.Write()
  Public = PublicKey(n, PubKey, Name, Address, Private)
  return Private, Public

class PublicKeyFile:
  """The PublicKeyFile class encapsulates the disk file which maintains a user's
public key and all their pertinent trust relationships."""

  def __init__(self, Filename, Public=None):
    "Constructor."
    self.Filename, self.Owner = Filename, None
    self.Trusted, self.Revoked = {}, {}
    if Public: self.Owner, self.Keys = Public.Key, {Public.Key: Public}

  def MyPublicKey(self): return self.Keys[self.Owner]

  def Write(self):
    "Write file to disk."
    F = open(self.Filename, "wb")
    try:
      F.write(MAGIC_PUB)
      WriteN(F, self.Owner, 16)
      WriteN(F, len(self.Keys), 2)
      for i in self.Keys: self.Keys[i].Write(F)
      WriteN(F, sum(map(lambda x: len(self.Trusted[x]), self.Trusted)), 2)
      for i in self.Trusted:
        for j in self.Trusted[i]:
          self.Trusted[i][j].Write(F)
      WriteN(F, sum(map(lambda x: len(self.Revoked[x]), self.Revoked)), 2)
      for i in self.Revoked:
        for j in self.Revoked[i]:
          self.Revoked[i][j].Write(F)
    finally:
      F.close()

  def Read(self):
    "Read file from disk."
    F = open(self.Filename, "rb")
    try:
      if F.read(4) != MAGIC_PUB: raise FileFormatError
      self.Owner = ReadN(F, 16)
      self.Keys = {}
      for i in range(ReadN(F, 2)):
        P = PublicKey.Read(F)
        self.Keys[P.Key] = P
      self.Trusted = {}
      for i in range(ReadN(F, 2)):
        T = TrustRelationship.Read(F)
        self.Trusted[T.Trustee] = self.Trusted.get(T.Trustee, {})
        self.Trusted[T.Trustee][T.Truster] = T
      self.Revoked = {}
      for i in range(ReadN(F, 2)):
        T = TrustRelationship.Read(F)
        self.Revoked[T.Trustee] = self.Revoked.get(T.Trustee, {})
        self.Revoked[T.Trustee][T.Truster] = T
    finally:
      F.close()

  def Merge(self, PubFile, Overwrite=False):
    "Merge a user's public keys and relationships into our key file."

    # If they didn't give us an object, assume it is a filename.
    if not isinstance(PubFile, PublicKeyFile):
      PubFile = PublicKeyFile(PubFile)
      PubFile.Read()

    # Copy all of the user's public keys into our file.
    for i in PubFile.Keys:
      if Overwrite or not self.Keys.has_key(i):
        self.Keys[i] = PubFile.Keys[i]

    # Copy all of the user's trust relationships into our file.
    for i in PubFile.Trusted:
      self.Trusted[i] = self.Trusted.get(i, {})
      for j in PubFile.Trusted[i]:
        if Overwrite or not self.Trusted[i].has_key(j):
          self.Trusted[i][j] = PubFile.Trusted[i][j]

    # Copy all of the user's trust revokations into our file.
    for i in PubFile.Revoked:
      self.Revoked[i] = self.Revoked.get(i, {})
      for j in PubFile.Revoked[i]:
        if Overwrite or not self.Revoked[i].has_key(j):
          self.Revoked[i][j] = PubFile.Revoked[i][j]

  def AddTrust(self, PubFilename, Private, Transferrable="N"):
    "Add a trust relationship with the user in the given public key file."

    # Read in trustee's public keyfile.
    P = PublicKeyFile(PubFilename)
    P.Read()

    # Put the user in our key list.
    self.Keys[P.Owner] = P.MyPublicKey()

    # Create a trust relationship where we trust the user we just loaded.
    T = TrustRelationship(self.MyPublicKey(), P.MyPublicKey(), Private,
      Transferrable)

    # Add the trust relationship to our list.
    self.Trusted[T.Trustee] = self.Trusted.get(T.Trustee, {})
    self.Trusted[T.Trustee][T.Truster] = T

    # Copy the user's public keys into ours.
    # Note: This does not make us trust who they trust.  It just helps us track
    #       who trusts whom.
    self.Merge(P)

  def RevokeTrust(self, Relationship):
    # Add a trust relationship to our Revoked list and remove it from Trusted."
    self.Revoked[Relationship.Trustee] = \
      self.Revoked.get(Relationship.Trustee, {})
    self.Revoked[Relationship.Trustee][Relationship.Truster] = Relationship
    try:
      del self.Trusted[Relationship.Trustee][Relationship.Truster]
      if not len(self.Trusted[Relationship.Trustee]):
        del self.Trusted[Relationship.Trustee]
    except KeyError:
      pass

class ModuleObject:
  "Used to wrap a module so it can be pickled."

  def __init__(self, Module):
    "Constructor."
    self.Name, self.File = Module.__name__, Module.__file__
    F = open(self.File, "rb")
    self.Data = F.read()
    F.close()

  def Import(self):
    "Import the file back in and return it."
    Ext = EXT_SEARCH.search(self.File).group(1)
    while True:
      Filename = "x%d" % random.randint(0,1000000000)
      L = glob.glob(Filename + Ext)
      if not L: break
    F = open(Filename + Ext, "wb")
    F.write(self.Data)
    F.close()
    Module = __import__(Filename)
    Module.__name__, Module.__file__ = self.Name, self.File
    os.unlink(Filename + Ext)
    if Ext == ".py": os.unlink(Filename + Ext + "c")
    return Module

class TPickle:
  """TPickle is the trusted pickle object.  It contains data, signatures, and
trust relationships."""

  def __init__(self, Filename):
    "Constructor."
    self.Filename = Filename
    self.Compress, self.Data = True, None
    self.Keys, self.Signatures, self.Trusted = {}, {}, {}

  def Read(self):
    "Read the trusted pickle from the file."
    F = open(self.Filename, "rb")
    try:
      Sig = F.read(4)
      if Sig == MAGIC_ZIP:
        self.Compress = True
        self.Data = zlib.decompress(ReadS(F))
      elif Sig == MAGIC_UNZIP:
        self.Compress = False
        self.Data = ReadS(F)
      else:
        raise FileFormatError
      self.Keys = {}
      for i in range(ReadN(F, 2)):
        K = PublicKey.Read(F)
        self.Keys[K.Key] = K
      self.Signatures = {}
      for i in range(ReadN(F, 2)):
        S = Signature.Read(F)
        self.Signatures[S.Signer] = S
      self.Trusted = {}
      for i in range(ReadN(F, 2)):
        T = TrustRelationship.Read(F)
        self.Trusted[T.Trustee] = self.Trusted.get(T.Trustee, {})
        self.Trusted[T.Trustee][T.Truster] = T
    finally:
      F.close()

  def Write(self):
    "Write the trusted pickle out to file."
    F = open(self.Filename, "wb")
    try:
      if self.Compress:
        F.write(MAGIC_ZIP)
        WriteS(F, zlib.compress(self.Data))
      else:
        F.write(MAGIC_UNZIP)
        WriteS(F, self.Data)
      WriteN(F, len(self.Keys), 2)
      for i in self.Keys:
        self.Keys[i].Write(F)
      WriteN(F, len(self.Signatures), 2)
      for i in self.Signatures:
        self.Signatures[i].Write(F)
      WriteN(F, sum(map(lambda x: len(self.Trusted[x]), self.Trusted)), 2)
      for i in self.Trusted:
        for j in self.Trusted[i]:
          self.Trusted[i][j].Write(F)
    finally:
      F.close()

  def SetCompression(self, Compress=True):
    self.Compress = Compress

  def TestSignatures(self, Trusted=[], Revoked=[]):
    "Test to see if the document has been signed by someone we trust."

    # Use set objects
    Trusted, Revoked = sets.Set(Trusted), sets.Set(Revoked)

    # Was it signed by anyone we trust?
    AllSigs = sets.Set(filter(lambda x: self.Signatures[x].Test(self.Data,
      self.Keys[self.Signatures[x].Signer]), self.Signatures))
    Sigs = AllSigs - Revoked
    RetVal = Sigs & Trusted
    if RetVal: return TRUSTED, map(lambda x: self.Keys[x], RetVal)

    # Do we have any transferrable trust?
    Found, Trusters = sets.Set(), Sigs.copy()
    for i in Trusters:
      if self.Trusted.has_key(i):
        for j in self.Trusted[i]:
          T = self.Trusted[i][j]
          if T.Test(): Found.add(T.Truster)
    Found = Trusters = Trusters | Found
    while Found:
      Found = sets.Set()
      for i in Trusters:
        if self.Trusted.has_key(i):
          for j in self.Trusted[i]:
            T = self.Trusted[i][j]
            if (T.Transferrable == "Y") and (T.Truster not in Trusters):
              if not T.Test(): continue
              Found.add(T.Truster)
      Trusters |= Found
    RetVal = list((Trusters & Trusted) - Revoked)
    if RetVal: return TRANSFERRED, map(lambda x: self.Keys[x], RetVal)

    # Are any of the signers revoked?
    RetVal = list(AllSigs & Revoked)
    if RetVal: return REVOKED, map(lambda x: self.Keys[x], RetVal)

    # Return the signers.
    return UNKNOWN, map(lambda x: self.Keys[x], Sigs)

  def Pickle(self, Data):
    "Construct the pickle from a data object."
    if type(Data) == ModuleType: Data = ModuleObject(Data)
    self.Data = cPickle.dumps(Data, -1)

  def Unpickle(self):
    "Deconstruct the pickle data into a data object."
    Data = cPickle.loads(self.Data)
    if isinstance(Data, ModuleObject): Data = Data.Import()
    return Data

  def Sign(self, PublicFile, Private, IncludeTrusts=False):
    "Sign the document."

    # Add our signature & key
    self.Signatures[PublicFile.Owner] = \
      Signature(self.Data, PublicFile, Private)
    self.Keys[PublicFile.Owner] = PublicFile.MyPublicKey()

    # Include those who trust us?
    if IncludeTrusts == True:
      Found, Trusters = sets.Set(), sets.Set([PublicFile.Owner])
      for i in Trusters:
        if PublicFile.Trusted.has_key(i):
          for j in PublicFile.Trusted[i]:
            T = PublicFile.Trusted[i][j]
            Found.add(T.Truster)
            self.Trusted[T.Trustee] = self.Trusted.get(T.Trustee, {})
            self.Trusted[T.Trustee][T.Truster] = T
            self.Keys[T.Truster] = PublicFile.Keys[T.Truster]
      Found = Trusters = sets.Set([PublicFile.Owner]) | Found
      while Found:
        Found = sets.Set()
        for i in Trusters:
          if PublicFile.Trusted.has_key(i):
            for j in PublicFile.Trusted[i]:
              T = PublicFile.Trusted[i][j]
              if (T.Transferrable == "Y") and (T.Truster not in Trusters):
                  Found.add(T.Truster)
                  self.Trusted[T.Trustee] = self.Trusted.get(T.Trustee, {})
                  self.Trusted[T.Trustee][T.Truster] = T
                  self.Keys[T.Truster] = PublicFile.Keys[T.Truster]
        Trusters |= Found

def NewKeys():
  "Interactively generate a new key pair. DO NOT AUTOMATE!"
  # This routine should not be automated because it relies on the unpredictable
  # amount of time between inputs to help seed the random number generator.
  # If you re-seed the random number generator immediately after picking a
  # random number, then you will end up with 52 bits worth of randomness.
  # Good key generation requires 256 bits worth of randomness.

  global GenSeed5x52

  random.seed()
  GenSeed5x52 = [long(random.randint(0, (1L << 52) - 1))]
  Name = raw_input("Your name: ")
  random.seed()
  GenSeed5x52.append(long(random.randint(0, (1L << 52) - 1)))
  Address = raw_input("Your e-mail address: ")
  random.seed()
  GenSeed5x52.append(long(random.randint(0, (1L << 52) - 1)))
  Base = raw_input("Key pair filename base (___.pub & ___.prv): ")
  random.seed()
  GenSeed5x52.append(long(random.randint(0, (1L << 52) - 1)))
  while True:
    Pass1 = getpass.getpass("Private key password (blank OK): ")
    if Pass1 == "": break
    Pass2 = getpass.getpass("Repeat password (for verification): ")
    if Pass1 == Pass2: break
  random.seed()
  GenSeed5x52.append(long(random.randint(0, (1L << 52) - 1)))
  Private, Public = GenKeys("%s.prv" % Base, Name, Address, Pass1)
  KeyFile = PublicKeyFile("%s.pub" % Base, Public)
  KeyFile.Write()
  