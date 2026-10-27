module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data3
import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data4

#kc_eval CFSG.KC.BM.Fi23 p9 CFSG.KC.BM.Twin.prod 4370 2412240 9562797788961859630 g16 g2 g11 g7
#kc_eval CFSG.KC.BM.Fi23 pi9 CFSG.KC.BM.Twin.inv 4370 0 0 p9
#kc_eval CFSG.KC.BM.Fi23 img9 CFSG.KC.BM.Twin.prod 4370 2412240 5737273078718957642 p9 D pi9
