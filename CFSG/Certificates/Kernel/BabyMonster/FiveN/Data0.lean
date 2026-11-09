module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
import CFSG.Certificates.Kernel.BabyMonster.Five.Data3
import CFSG.Certificates.Kernel.BabyMonster.Five.Data4
import CFSG.Certificates.Kernel.BabyMonster.Five.Data10
import CFSG.Certificates.Kernel.BabyMonster.Five.Data12
import CFSG.Certificates.Kernel.BabyMonster.Five.Data14
import CFSG.Certificates.Kernel.BabyMonster.Five.Data16
import CFSG.Certificates.Kernel.BabyMonster.Five.Data18
import CFSG.Certificates.Kernel.BabyMonster.Five.Data19

#kc_eval CFSG.KC.BM.FiveN n0a CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Five.f86 CFSG.KC.BM.Five.f85_sq2 CFSG.KC.BM.Five.f86_sq1
#kc_eval CFSG.KC.BM.FiveN n0b CFSG.KC.BM.Twin.prod 4370 0 0 n0a CFSG.KC.BM.Five.f85_sq2 CFSG.KC.BM.Five.f85_sq2
#kc_eval CFSG.KC.BM.FiveN n0 CFSG.KC.BM.Twin.prod 4370 0 0 n0b CFSG.KC.BM.Five.f86 CFSG.KC.BM.Five.f85_sq2
#kc_eval CFSG.KC.BM.FiveN n1a CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Five.f86 CFSG.KC.BM.Five.f85_sq2 CFSG.KC.BM.Five.f85_sq2
#kc_eval CFSG.KC.BM.FiveN n1b CFSG.KC.BM.Twin.prod 4370 0 0 n1a CFSG.KC.BM.Five.f86_sq1 CFSG.KC.BM.Five.f85_sq2
#kc_eval CFSG.KC.BM.FiveN n1c CFSG.KC.BM.Twin.prod 4370 0 0 n1b CFSG.KC.BM.Five.f86_sq1 CFSG.KC.BM.Five.f85_sq2
#kc_eval CFSG.KC.BM.FiveN n1d CFSG.KC.BM.Twin.prod 4370 0 0 n1c CFSG.KC.BM.Five.f86 CFSG.KC.BM.Five.f85
#kc_eval CFSG.KC.BM.FiveN n1 CFSG.KC.BM.Twin.prod 4370 0 0 n1d CFSG.KC.BM.Five.H3
#kc_eval CFSG.KC.BM.FiveN n2a CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Five.oh_p CFSG.KC.BM.Five.oh_p CFSG.KC.BM.Five.f85
#kc_eval CFSG.KC.BM.FiveN n2b CFSG.KC.BM.Twin.prod 4370 0 0 n2a CFSG.KC.BM.Five.oh_p CFSG.KC.BM.Five.f85
#kc_eval CFSG.KC.BM.FiveN n2 CFSG.KC.BM.Twin.prod 4370 0 0 n2b CFSG.KC.BM.Five.f86 CFSG.KC.BM.Five.f85
#kc_eval CFSG.KC.BM.FiveN e0a CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Five.f85_sq2 CFSG.KC.BM.Five.W_sq3 CFSG.KC.BM.Five.Q2_sq1
#kc_eval CFSG.KC.BM.FiveN e0b CFSG.KC.BM.Twin.prod 4370 0 0 e0a CFSG.KC.BM.Five.Q3_sq2 CFSG.KC.BM.Five.Q4_sq1
#kc_eval CFSG.KC.BM.FiveN e0 CFSG.KC.BM.Twin.prod 4370 0 0 e0b CFSG.KC.BM.Five.Q4 CFSG.KC.BM.Five.Zp3
#kc_eval CFSG.KC.BM.FiveN e1a CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Five.f85_sq1 CFSG.KC.BM.Five.W_sq3_sq2 CFSG.KC.BM.Five.Q2_sq2
#kc_eval CFSG.KC.BM.FiveN e1b CFSG.KC.BM.Twin.prod 4370 0 0 e1a CFSG.KC.BM.Five.Q3 CFSG.KC.BM.Five.Q4_sq1
#kc_eval CFSG.KC.BM.FiveN e1 CFSG.KC.BM.Twin.prod 4370 0 0 e1b CFSG.KC.BM.Five.Q4 CFSG.KC.BM.Five.Zp4
#kc_eval CFSG.KC.BM.FiveN e2a CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Five.f85_sq2 CFSG.KC.BM.Five.Q1e3 CFSG.KC.BM.Five.Q3_sq1
#kc_eval CFSG.KC.BM.FiveN e2 CFSG.KC.BM.Twin.prod 4370 0 0 e2a CFSG.KC.BM.Five.Q4_sq2 CFSG.KC.BM.Five.Z
#kc_eval CFSG.KC.BM.FiveN m0 CFSG.KC.BM.Twin.prod 4370 0 0 n0 CFSG.KC.BM.Five.f85
#kc_eval CFSG.KC.BM.FiveN m1 CFSG.KC.BM.Twin.prod 4370 0 0 n1 CFSG.KC.BM.Five.f85
#kc_eval CFSG.KC.BM.FiveN m2 CFSG.KC.BM.Twin.prod 4370 0 0 n2 CFSG.KC.BM.Five.f85
