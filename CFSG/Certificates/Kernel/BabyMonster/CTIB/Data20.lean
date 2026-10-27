module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data19
import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data2
import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data7
import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data9
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data6
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data3

#kc_eval CFSG.KC.BM.CTIB W12_1 CFSG.KC.BM.Twin.prod 4370 2412240 7490345550061048144 W12_0 CFSG.KC.BM.Max2.G2 CFSG.KC.BM.Max2.G2
#kc_eval CFSG.KC.BM.CTIB W12_2 CFSG.KC.BM.Twin.prod 4370 2412240 127783517682707212 W12_1 CFSG.KC.BM.NativePair.Q25 CFSG.KC.BM.Max2.Gi2
#kc_eval CFSG.KC.BM.CTIB W12 CFSG.KC.BM.Twin.prod 4370 2412240 4762454230282477468 W12_2 CFSG.KC.BM.Max2.Gi2 Tau2
#kc_eval CFSG.KC.BM.CTIB W12_inv CFSG.KC.BM.Twin.inv 4370 0 0 W12
#kc_eval CFSG.KC.BM.CTIB Cj12 CFSG.KC.BM.Twin.prod 4370 2412240 15284613466493999812 W12_inv R12 W12
#kc_eval CFSG.KC.BM.CTIB Pf12 CFSG.KC.BM.Twin.prod 4370 2412240 13601683778303707740 R3 Cj12
#kc_eval CFSG.KC.BM.CTIB Pf12_sq1 CFSG.KC.BM.Twin.prod 4370 2412240 3224944333520727768 Pf12 Pf12
#kc_eval CFSG.KC.BM.CTIB Pf12_sq2 CFSG.KC.BM.Twin.prod 4370 2412240 3492464446567161057 Pf12_sq1 Pf12_sq1
#kc_eval CFSG.KC.BM.CTIB Pf12_sq3 CFSG.KC.BM.Twin.prod 4370 2412240 7650606536162813684 Pf12_sq2 Pf12_sq2
