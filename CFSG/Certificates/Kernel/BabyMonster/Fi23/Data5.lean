module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data1
import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data3
import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data4

#kc_eval CFSG.KC.BM.Fi23 p0 CFSG.KC.BM.Twin.prod 4370 2412240 1453678947277618888 V g12 g7 g9
#kc_eval CFSG.KC.BM.Fi23 pi0 CFSG.KC.BM.Twin.inv 4370 0 0 p0
#kc_eval CFSG.KC.BM.Fi23 img0 CFSG.KC.BM.Twin.prod 4370 2412240 5381777288364536348 p0 D pi0
