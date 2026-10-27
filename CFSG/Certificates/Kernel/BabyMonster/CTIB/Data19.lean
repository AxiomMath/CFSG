module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data18
import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data7
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data4
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data5
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data6
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data3

#kc_eval CFSG.KC.BM.CTIB Pf10_sq4 CFSG.KC.BM.Twin.prod 4370 2412240 16413283127333048637 Pf10_sq3 Pf10_sq3
#kc_eval CFSG.KC.BM.CTIB W11_0 CFSG.KC.BM.Twin.prod 4370 2412240 16791250575512102184 CFSG.KC.BM.NativePair.Q25 CFSG.KC.BM.Max2.Gi2 CFSG.KC.BM.NativePair.Q25
#kc_eval CFSG.KC.BM.CTIB W11 CFSG.KC.BM.Twin.prod 4370 2412240 7107612536804494797 W11_0 CFSG.KC.BM.Max2.G1
#kc_eval CFSG.KC.BM.CTIB W11_inv CFSG.KC.BM.Twin.inv 4370 0 0 W11
#kc_eval CFSG.KC.BM.CTIB Cj11 CFSG.KC.BM.Twin.prod 4370 2412240 10707926288020650221 W11_inv R11 W11
#kc_eval CFSG.KC.BM.CTIB Pf11 CFSG.KC.BM.Twin.prod 4370 2412240 4994226855021274049 CFSG.KC.BM.Max2.Xb Cj11
#kc_eval CFSG.KC.BM.CTIB Pf11_sq1 CFSG.KC.BM.Twin.prod 4370 2412240 651096725699063572 Pf11 Pf11
#kc_eval CFSG.KC.BM.CTIB Pf11_sq2 CFSG.KC.BM.Twin.prod 4370 2412240 17876459471196845749 Pf11_sq1 Pf11_sq1
#kc_eval CFSG.KC.BM.CTIB W12_0 CFSG.KC.BM.Twin.prod 4370 2412240 3108667127682624896 CFSG.KC.BM.Max2.G1 CFSG.KC.BM.NativePair.Q25 CFSG.KC.BM.Max2.G2
