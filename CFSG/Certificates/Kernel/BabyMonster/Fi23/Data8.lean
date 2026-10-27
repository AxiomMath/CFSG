module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data3
import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data4

#kc_eval CFSG.KC.BM.Fi23 p3 CFSG.KC.BM.Twin.prod 4370 2412240 1607178636056198384 g4 g8
#kc_eval CFSG.KC.BM.Fi23 pi3 CFSG.KC.BM.Twin.inv 4370 0 0 p3
#kc_eval CFSG.KC.BM.Fi23 img3 CFSG.KC.BM.Twin.prod 4370 2412240 11706508599887505315 p3 D pi3
