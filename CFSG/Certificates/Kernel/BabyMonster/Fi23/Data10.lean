module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data3
import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data4

#kc_eval CFSG.KC.BM.Fi23 p5 CFSG.KC.BM.Twin.prod 4370 2412240 4609145184753129044 g0 g12 g15
#kc_eval CFSG.KC.BM.Fi23 pi5 CFSG.KC.BM.Twin.inv 4370 0 0 p5
#kc_eval CFSG.KC.BM.Fi23 img5 CFSG.KC.BM.Twin.prod 4370 2412240 17857070929843854994 p5 D pi5
