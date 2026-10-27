module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data1
import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data3
import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data4

#kc_eval CFSG.KC.BM.Fi23 p6 CFSG.KC.BM.Twin.prod 4370 2412240 14967363442962847745 V g11 g2 g4 g9
#kc_eval CFSG.KC.BM.Fi23 pi6 CFSG.KC.BM.Twin.inv 4370 0 0 p6
#kc_eval CFSG.KC.BM.Fi23 img6 CFSG.KC.BM.Twin.prod 4370 2412240 13175952161629428402 p6 D pi6
