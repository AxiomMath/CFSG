module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data2
import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data3
import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data4

#kc_eval CFSG.KC.BM.Fi23 p1 CFSG.KC.BM.Twin.prod 4370 2412240 11639089026550162574 U g4 g13
#kc_eval CFSG.KC.BM.Fi23 pi1 CFSG.KC.BM.Twin.inv 4370 0 0 p1
#kc_eval CFSG.KC.BM.Fi23 img1 CFSG.KC.BM.Twin.prod 4370 2412240 8884396576002597147 p1 D pi1
