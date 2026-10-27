module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data3
import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data4

#kc_eval CFSG.KC.BM.Fi23 p2 CFSG.KC.BM.Twin.prod 4370 2412240 11826236780911662675 g11 g10 g14 g14 g1
#kc_eval CFSG.KC.BM.Fi23 pi2 CFSG.KC.BM.Twin.inv 4370 0 0 p2
#kc_eval CFSG.KC.BM.Fi23 img2 CFSG.KC.BM.Twin.prod 4370 2412240 15022924465107123830 p2 D pi2
