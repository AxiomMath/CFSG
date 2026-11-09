module

import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Th.S.Chars
public import Certificates.Data.CFSGNative.Th.Data
import CFSG.Certificates.Kernel.Common.NatItems
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

#th_chars CFSG.KD.ThSeed.LA CFSG.Sporadic.Th.Native.seedA
#th_chars CFSG.KD.ThSeed.LB CFSG.Sporadic.Th.Native.seedB

#kc_repo #kc_nat_items CFSG.KD.ThSeed
    "CFSG/Certificates/Kernel/Th/S/Data/data/Seed_const.items" 47636 10674603790107308401
    SA SB SF SAf SFf SFx
