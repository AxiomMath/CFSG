module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
meta import CFSG.Certificates.Kernel.BabyMonster.TwinRank
import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data1
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data6
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data7
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data8

#kc_eval CFSG.KC.BM.CTIB R13_0 CFSG.KC.BM.Twin.prod 4370 2412240 16156139031806220257 H10 CFSG.KC.BM.Max2.E1 CFSG.KC.BM.Max2.E2
#kc_eval CFSG.KC.BM.CTIB R13_1 CFSG.KC.BM.Twin.prod 4370 2412240 4560156095435900550 R13_0 CFSG.KC.BM.Max2.E4 CFSG.KC.BM.Max2.E5
#kc_eval CFSG.KC.BM.CTIB R13_2 CFSG.KC.BM.Twin.prod 4370 2412240 13208606032555836848 R13_1 CFSG.KC.BM.Max2.E6 CFSG.KC.BM.Max2.E7
#kc_eval CFSG.KC.BM.CTIB R13 CFSG.KC.BM.Twin.prod 4370 2412240 15418067973837185390 R13_2 CFSG.KC.BM.Max2.E8 CFSG.KC.BM.Max2.E16
#kc_eval CFSG.KC.BM.CTIB Pr13 CFSG.KC.BM.Twin.rank 4370 2412240 13799090323762846851 R13 1 1
#kc_eval CFSG.KC.BM.CTIB Qr13 CFSG.KC.BM.Twin.polyMul 4370 2412240 1800790984810477565 Pr13 R13 1 1
