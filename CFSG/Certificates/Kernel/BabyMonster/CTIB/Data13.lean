module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data12
import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data5
import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data9
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data4
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data5
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data6

#kc_eval CFSG.KC.BM.CTIB W7_1 CFSG.KC.BM.Twin.prod 4370 2412240 8287717450134025204 W7_0 Tau2 CFSG.KC.BM.Max2.Gi2
#kc_eval CFSG.KC.BM.CTIB W7_2 CFSG.KC.BM.Twin.prod 4370 2412240 13525866933837704146 W7_1 CFSG.KC.BM.Max2.G1 Tau2
#kc_eval CFSG.KC.BM.CTIB W7_3 CFSG.KC.BM.Twin.prod 4370 2412240 12046308572198788259 W7_2 Tau2 CFSG.KC.BM.Max2.G2
#kc_eval CFSG.KC.BM.CTIB W7_4 CFSG.KC.BM.Twin.prod 4370 2412240 9961544914612142141 W7_3 CFSG.KC.BM.Max2.G2 Tau2
#kc_eval CFSG.KC.BM.CTIB W7 CFSG.KC.BM.Twin.prod 4370 2412240 11880503847296322542 W7_4 Tau2
#kc_eval CFSG.KC.BM.CTIB W7_inv CFSG.KC.BM.Twin.inv 4370 0 0 W7
#kc_eval CFSG.KC.BM.CTIB Cj7 CFSG.KC.BM.Twin.prod 4370 2412240 4753994359830562050 W7_inv R7 W7
#kc_eval CFSG.KC.BM.CTIB Pf7 CFSG.KC.BM.Twin.prod 4370 2412240 14715170685165408253 CFSG.KC.BM.Max2.Xb Cj7
#kc_eval CFSG.KC.BM.CTIB Pf7_sq1 CFSG.KC.BM.Twin.prod 4370 2412240 16570235928042331545 Pf7 Pf7
