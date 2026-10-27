module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data1
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data0
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data1
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data2
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data3

#kc_eval CFSG.KC.BM.Max2 R4 CFSG.KC.BM.Twin.prod 4370 2412240 13271570295259762728 r4_sq3 r4_sq4
#kc_eval CFSG.KC.BM.Max2 Z CFSG.KC.BM.Twin.prod 4370 2412240 3123139598342412480 CFSG.KC.BM.NativePair.T R4 CFSG.KC.BM.NativePair.T_inv
#kc_eval CFSG.KC.BM.Max2 Wp_0 CFSG.KC.BM.Twin.prod 4370 2412240 3876728623300831312 CFSG.KC.BM.NativePair.Q23 CFSG.KC.BM.NativePair.Q2 CFSG.KC.BM.NativePair.Q10
#kc_eval CFSG.KC.BM.Max2 Wp_1 CFSG.KC.BM.Twin.prod 4370 2412240 1219044773745537727 Wp_0 CFSG.KC.BM.NativePair.Q22 CFSG.KC.BM.NativePair.Q17
#kc_eval CFSG.KC.BM.Max2 Wp_2 CFSG.KC.BM.Twin.prod 4370 2412240 15969120415882840994 Wp_1 CFSG.KC.BM.NativePair.Q7 CFSG.KC.BM.NativePair.Q2
#kc_eval CFSG.KC.BM.Max2 Wp_3 CFSG.KC.BM.Twin.prod 4370 2412240 2418823311611984586 Wp_2 CFSG.KC.BM.NativePair.Q15 CFSG.KC.BM.NativePair.Q13
#kc_eval CFSG.KC.BM.Max2 Wp_4 CFSG.KC.BM.Twin.prod 4370 2412240 17339411123041008011 Wp_3 CFSG.KC.BM.NativePair.Q17 CFSG.KC.BM.NativePair.Q7
#kc_eval CFSG.KC.BM.Max2 Wp_5 CFSG.KC.BM.Twin.prod 4370 2412240 17991152280683766780 Wp_4 CFSG.KC.BM.NativePair.Q24 CFSG.KC.BM.NativePair.Q2
