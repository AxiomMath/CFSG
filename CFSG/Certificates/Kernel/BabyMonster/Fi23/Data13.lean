module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data1
import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data3
import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data4

#kc_eval CFSG.KC.BM.Fi23 p8 CFSG.KC.BM.Twin.prod 4370 2412240 10017343363341682309 g13 g15 V
#kc_eval CFSG.KC.BM.Fi23 pi8 CFSG.KC.BM.Twin.inv 4370 0 0 p8
#kc_eval CFSG.KC.BM.Fi23 img8 CFSG.KC.BM.Twin.prod 4370 2412240 6435196684714370025 p8 D pi8
