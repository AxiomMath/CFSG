module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data2
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data4
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data5
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data6
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data3

#kc_eval CFSG.KC.BM.CTIB Tau2 CFSG.KC.BM.Twin.prod 4370 2412240 7980750208150540061 CFSG.KC.BM.NativePair.Q25 CFSG.KC.BM.NativePair.Q25
#kc_eval CFSG.KC.BM.CTIB W2_0 CFSG.KC.BM.Twin.prod 4370 2412240 3108667127682624896 CFSG.KC.BM.Max2.G1 CFSG.KC.BM.NativePair.Q25 CFSG.KC.BM.Max2.G2
#kc_eval CFSG.KC.BM.CTIB W2_1 CFSG.KC.BM.Twin.prod 4370 2412240 6004744290557443461 W2_0 CFSG.KC.BM.Max2.G1 CFSG.KC.BM.NativePair.Q25
#kc_eval CFSG.KC.BM.CTIB W2_2 CFSG.KC.BM.Twin.prod 4370 2412240 8734225347535801109 W2_1 CFSG.KC.BM.Max2.G1 Tau2
#kc_eval CFSG.KC.BM.CTIB W2_3 CFSG.KC.BM.Twin.prod 4370 2412240 3899034243510603685 W2_2 CFSG.KC.BM.Max2.G2 Tau2
#kc_eval CFSG.KC.BM.CTIB W2 CFSG.KC.BM.Twin.prod 4370 2412240 4068930599424611270 W2_3 CFSG.KC.BM.Max2.G2 Tau2
#kc_eval CFSG.KC.BM.CTIB W2_inv CFSG.KC.BM.Twin.inv 4370 0 0 W2
#kc_eval CFSG.KC.BM.CTIB Cj2 CFSG.KC.BM.Twin.prod 4370 2412240 12007174692087780612 W2_inv R2 W2
#kc_eval CFSG.KC.BM.CTIB Pf2 CFSG.KC.BM.Twin.prod 4370 2412240 4100343116136603431 CFSG.KC.BM.Max2.Xb Cj2
