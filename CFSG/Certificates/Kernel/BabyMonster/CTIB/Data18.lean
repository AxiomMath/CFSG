module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data2
import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data6
import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data9
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data5
import CFSG.Certificates.Kernel.BabyMonster.Max2.Data6

#kc_eval CFSG.KC.BM.CTIB W10_0 CFSG.KC.BM.Twin.prod 4370 2412240 8105312655023508818 CFSG.KC.BM.Max2.G1 Tau2 Tau2
#kc_eval CFSG.KC.BM.CTIB W10_1 CFSG.KC.BM.Twin.prod 4370 2412240 10643753618190483174 W10_0 CFSG.KC.BM.Max2.Gi2 Tau2
#kc_eval CFSG.KC.BM.CTIB W10 CFSG.KC.BM.Twin.prod 4370 2412240 13654563875482635901 W10_1 CFSG.KC.BM.Max2.G2 Tau2
#kc_eval CFSG.KC.BM.CTIB W10_inv CFSG.KC.BM.Twin.inv 4370 0 0 W10
#kc_eval CFSG.KC.BM.CTIB Cj10 CFSG.KC.BM.Twin.prod 4370 2412240 13529561628849844630 W10_inv R10 W10
#kc_eval CFSG.KC.BM.CTIB Pf10 CFSG.KC.BM.Twin.prod 4370 2412240 1466160990683388713 R3 Cj10
#kc_eval CFSG.KC.BM.CTIB Pf10_sq1 CFSG.KC.BM.Twin.prod 4370 2412240 11804555941202309946 Pf10 Pf10
#kc_eval CFSG.KC.BM.CTIB Pf10_sq2 CFSG.KC.BM.Twin.prod 4370 2412240 15635462218098679131 Pf10_sq1 Pf10_sq1
#kc_eval CFSG.KC.BM.CTIB Pf10_sq3 CFSG.KC.BM.Twin.prod 4370 2412240 100656391975103466 Pf10_sq2 Pf10_sq2
