# TrustedPickle with Read_Mem
#### Allows you to read your keys from memory instead of a file


Had a tough time making a python binary which inlcuded the key files from the trusted pickle.  Decided to modify the TrustedPickle package to read the keys from memory.

####To use:

    Use the code in 'make_embbed_sig.txt' in command line to generate the keys.

    Update Python_sigs.py with these keys.

    Import the Python_sigs module in your code.

    Pass empty (or whatever filenames) into your code.  I.e. Pubkey = TrustedPickle.PublicKeyFile('')

    Read with the Read_Mem functions.  I.e. Pubkey.Read_Mem(pub_key)


That's it!

Original readme below...



# TrustedPickle
This is a Github mirror for the awesome TrustedPickle package!  See the proper website below.

TrustedPickle
Copyright (C) 2003 Gre7g Luterman <gre7g@wolfhome.com>

This software is OSI Certified Open Source Software.
OSI Certified is a certification mark of the Open Source Initiative.

TrustedPickle is a Python module that allows you to use public and private keys
to sign pickle files. It does not use encryption, so it is legal to import and
export.

For more information, visit the TrustedPickle homepage:

    http://trustedpickle.sourceforge.net/

Installation instructions can be found on the TrustedPickle homepage.

ChangeLog tracks what major things were added, when, and by whom.

COPYING contains licensing information.
