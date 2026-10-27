module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data13
import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data9
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data5
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data6
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data3

#kc_eval CFSG.KC.BM.CTIB Pf7_sq2 CFSG.KC.BM.Twin.prod 4370 2412240 17186563181820381188 Pf7_sq1 Pf7_sq1
#kc_eval CFSG.KC.BM.CTIB W8_0 CFSG.KC.BM.Twin.prod 4370 2412240 11451610532484248442 Tau2 CFSG.KC.BM.Max2.G2 Tau2
#kc_eval CFSG.KC.BM.CTIB W8_1 CFSG.KC.BM.Twin.prod 4370 2412240 4039113823583133488 W8_0 CFSG.KC.BM.Max2.Gi2 CFSG.KC.BM.NativePair.Q25
#kc_eval CFSG.KC.BM.CTIB W8_2 CFSG.KC.BM.Twin.prod 4370 2412240 14732646185199092788 W8_1 CFSG.KC.BM.NativePair.Q25 CFSG.KC.BM.Max2.G1
#kc_eval CFSG.KC.BM.CTIB W8_3 CFSG.KC.BM.Twin.prod 4370 2412240 8661406282428963385 W8_2 CFSG.KC.BM.Max2.Gi2 CFSG.KC.BM.Max2.G1
#kc_eval CFSG.KC.BM.CTIB W8_4 CFSG.KC.BM.Twin.prod 4370 2412240 3119690788876091800 W8_3 Tau2 CFSG.KC.BM.Max2.Gi2
#kc_eval CFSG.KC.BM.CTIB W8_5 CFSG.KC.BM.Twin.prod 4370 2412240 10534081363142591470 W8_4 CFSG.KC.BM.Max2.Gi2 CFSG.KC.BM.Max2.Gi2
#kc_eval CFSG.KC.BM.CTIB W8 CFSG.KC.BM.Twin.prod 4370 2412240 6195458650809608154 W8_5 Tau2
#kc_eval CFSG.KC.BM.CTIB W8_inv CFSG.KC.BM.Twin.inv 4370 0 0 W8
