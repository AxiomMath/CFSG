module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
meta import CFSG.Certificates.Kernel.BabyMonster.TwinRank
import CFSG.Certificates.Kernel.BabyMonster.Five.Data3
import CFSG.Certificates.Kernel.BabyMonster.Five.Data4
import CFSG.Certificates.Kernel.BabyMonster.Five.Data10
import CFSG.Certificates.Kernel.BabyMonster.Five.Data12
import CFSG.Certificates.Kernel.BabyMonster.Five.Data16
import CFSG.Certificates.Kernel.BabyMonster.Five.Data18
import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data10
import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data11

#kc_eval CFSG.KC.BM.FiveA v69 CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Five.W_sq3_sq2 CFSG.KC.BM.Five.Q2_sq2 CFSG.KC.BM.Five.f85_sq2 CFSG.KC.BM.Five.Q4_sq2 p68 CFSG.KC.BM.Five.Q3_sq2 CFSG.KC.BM.Five.f85_sq2
#kc_eval CFSG.KC.BM.FiveA v71a CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Five.f85 CFSG.KC.BM.Five.Q3 CFSG.KC.BM.Five.f85_sq1
#kc_eval CFSG.KC.BM.FiveA v71b CFSG.KC.BM.Twin.prod 4370 0 0 v71a CFSG.KC.BM.Five.Q4 CFSG.KC.BM.Five.f85
#kc_eval CFSG.KC.BM.FiveA v71 CFSG.KC.BM.Twin.prod 4370 0 0 v71b CFSG.KC.BM.Five.Q2 CFSG.KC.BM.Five.W_sq3
#kc_eval CFSG.KC.BM.FiveA v72 CFSG.KC.BM.Twin.prod 4370 0 0 v69 v70 v71
#kc_eval CFSG.KC.BM.FiveA v112 CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Five.f85 CFSG.KC.BM.Five.Z
#kc_eval CFSG.KC.BM.FiveA PrkZ CFSG.KC.BM.Twin.rank 4370 0 0 CFSG.KC.BM.Five.Z 1 1
#kc_eval CFSG.KC.BM.FiveA RrkZ CFSG.KC.BM.Twin.polyMul 4370 0 0 PrkZ CFSG.KC.BM.Five.Z 1 1
