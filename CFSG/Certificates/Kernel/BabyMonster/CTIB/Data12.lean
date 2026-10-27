module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data4
import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data9
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data5
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data6
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data0
import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data3

#kc_eval CFSG.KC.BM.CTIB W6_0 CFSG.KC.BM.Twin.prod 4370 2412240 17714665668228338376 CFSG.KC.BM.NativePair.Q25 CFSG.KC.BM.Max2.G1 CFSG.KC.BM.Max2.Gi2
#kc_eval CFSG.KC.BM.CTIB W6_1 CFSG.KC.BM.Twin.prod 4370 2412240 2385278338397485298 W6_0 Tau2 Tau2
#kc_eval CFSG.KC.BM.CTIB W6_2 CFSG.KC.BM.Twin.prod 4370 2412240 15231388115349343163 W6_1 CFSG.KC.BM.Max2.G2 Tau2
#kc_eval CFSG.KC.BM.CTIB W6 CFSG.KC.BM.Twin.prod 4370 2412240 2370039212599947524 W6_2 CFSG.KC.BM.Max2.G1 Tau2
#kc_eval CFSG.KC.BM.CTIB W6_inv CFSG.KC.BM.Twin.inv 4370 0 0 W6
#kc_eval CFSG.KC.BM.CTIB Cj6 CFSG.KC.BM.Twin.prod 4370 2412240 17288882585972829866 W6_inv R6 W6
#kc_eval CFSG.KC.BM.CTIB Pf6 CFSG.KC.BM.Twin.prod 4370 2412240 6801106533714702291 CFSG.KC.BM.NativePair.Q0 Cj6
#kc_eval CFSG.KC.BM.CTIB Pf6p CFSG.KC.BM.Twin.prod 4370 2412240 10925885640012181371 Pf6 Pf6
#kc_eval CFSG.KC.BM.CTIB W7_0 CFSG.KC.BM.Twin.prod 4370 2412240 608389742647841845 CFSG.KC.BM.NativePair.Q25 CFSG.KC.BM.Max2.Gi2 CFSG.KC.BM.Max2.Gi2
