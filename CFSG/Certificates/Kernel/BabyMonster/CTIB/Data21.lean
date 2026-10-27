module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data20
import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data3
import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data8
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data5
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data6
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data3

#kc_eval CFSG.KC.BM.CTIB Pf12_sq4 CFSG.KC.BM.Twin.prod 4370 2412240 11030506651107245860 Pf12_sq3 Pf12_sq3
#kc_eval CFSG.KC.BM.CTIB Pf12p CFSG.KC.BM.Twin.prod 4370 2412240 12709809182529848102 Pf12_sq2 Pf12_sq4
#kc_eval CFSG.KC.BM.CTIB W13_0 CFSG.KC.BM.Twin.prod 4370 2412240 8689709839110707394 CFSG.KC.BM.Max2.G1 CFSG.KC.BM.NativePair.Q25 CFSG.KC.BM.NativePair.Q25
#kc_eval CFSG.KC.BM.CTIB W13_1 CFSG.KC.BM.Twin.prod 4370 2412240 7777473561485779462 W13_0 CFSG.KC.BM.Max2.G1 CFSG.KC.BM.Max2.Gi2
#kc_eval CFSG.KC.BM.CTIB W13_2 CFSG.KC.BM.Twin.prod 4370 2412240 16754288636363346926 W13_1 CFSG.KC.BM.Max2.G1 CFSG.KC.BM.Max2.G2
#kc_eval CFSG.KC.BM.CTIB W13 CFSG.KC.BM.Twin.prod 4370 2412240 14640841518224754526 W13_2 CFSG.KC.BM.NativePair.Q25
#kc_eval CFSG.KC.BM.CTIB W13_inv CFSG.KC.BM.Twin.inv 4370 0 0 W13
#kc_eval CFSG.KC.BM.CTIB Cj13 CFSG.KC.BM.Twin.prod 4370 2412240 14121227254973321625 W13_inv R13 W13
#kc_eval CFSG.KC.BM.CTIB Pf13 CFSG.KC.BM.Twin.prod 4370 2412240 677729439221781533 R5 Cj13
