module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data3
import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data4

#kc_eval CFSG.KC.BM.Fi23 p7 CFSG.KC.BM.Twin.prod 4370 2412240 12986646195548812306 g16 g0 g7 g7 g6 g4 g1
#kc_eval CFSG.KC.BM.Fi23 pi7 CFSG.KC.BM.Twin.inv 4370 0 0 p7
#kc_eval CFSG.KC.BM.Fi23 img7 CFSG.KC.BM.Twin.prod 4370 2412240 15384212066751868289 p7 D pi7
