module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
meta import CFSG.Certificates.Kernel.BabyMonster.TwinRank
import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data1
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data6
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data7
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data8
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data0

#kc_eval CFSG.KC.BM.CTIB R6_0 CFSG.KC.BM.Twin.prod 4370 2412240 6015593925228724476 H6 CFSG.KC.BM.NativePair.Q0 CFSG.KC.BM.Max2.E2
#kc_eval CFSG.KC.BM.CTIB R6_1 CFSG.KC.BM.Twin.prod 4370 2412240 3692005148413169765 R6_0 CFSG.KC.BM.Max2.E3 CFSG.KC.BM.Max2.E5
#kc_eval CFSG.KC.BM.CTIB R6_2 CFSG.KC.BM.Twin.prod 4370 2412240 10322083376570444685 R6_1 CFSG.KC.BM.Max2.E8 CFSG.KC.BM.Max2.E11
#kc_eval CFSG.KC.BM.CTIB R6 CFSG.KC.BM.Twin.prod 4370 2412240 18297845947962271394 R6_2 CFSG.KC.BM.Max2.E13
#kc_eval CFSG.KC.BM.CTIB Pr6 CFSG.KC.BM.Twin.rank 4370 2412240 15844052245885659626 R6 1 1
#kc_eval CFSG.KC.BM.CTIB Qr6 CFSG.KC.BM.Twin.polyMul 4370 2412240 1806680797224643072 Pr6 R6 1 1
#kc_eval CFSG.KC.BM.CTIB R7_0 CFSG.KC.BM.Twin.prod 4370 2412240 6015593925228724476 H6 CFSG.KC.BM.NativePair.Q0 CFSG.KC.BM.Max2.E2
