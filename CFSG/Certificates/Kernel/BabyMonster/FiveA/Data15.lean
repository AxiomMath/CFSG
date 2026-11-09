module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Five.Data3
import CFSG.Certificates.Kernel.BabyMonster.Five.Data4
import CFSG.Certificates.Kernel.BabyMonster.Five.Data12
import CFSG.Certificates.Kernel.BabyMonster.Five.Data16
import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data10

#kc_eval CFSG.KC.BM.FiveA b4 CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Five.Q2 CFSG.KC.BM.Five.Q3
#kc_eval CFSG.KC.BM.FiveA v27 CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Five.Q3 CFSG.KC.BM.Five.Q4
#kc_eval CFSG.KC.BM.FiveA v98 CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Five.Q2 CFSG.KC.BM.Five.W_sq3_sq2 CFSG.KC.BM.Five.Q3
#kc_eval CFSG.KC.BM.FiveA v100 CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Five.Q3_sq2 CFSG.KC.BM.Five.W_sq3 CFSG.KC.BM.Five.Q2_sq2
#kc_eval CFSG.KC.BM.FiveA v103 CFSG.KC.BM.Twin.prod 4370 0 0 v98 v99 v100
