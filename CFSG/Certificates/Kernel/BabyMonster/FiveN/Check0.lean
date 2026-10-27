module

import CFSG.Certificates.Kernel.BabyMonster.Load
import CFSG.Certificates.Kernel.BabyMonster.LoadFour
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data11
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data14
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data18
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data19
public import CFSG.Certificates.Kernel.BabyMonster.FiveN.Data0

#bm_mul4 CFSG.KC.BM.FiveN cn0 CFSG.KC.BM.Five.f86 [CFSG.KC.BM.Five.f85_sq2 CFSG.KC.BM.Five.f86_sq1 CFSG.KC.BM.Five.f85_sq2 CFSG.KC.BM.Five.f85_sq2 CFSG.KC.BM.Five.f86 CFSG.KC.BM.Five.f85_sq2] n0 []
#bm_mul4 CFSG.KC.BM.FiveN cn1 CFSG.KC.BM.Five.f86 [CFSG.KC.BM.Five.f85_sq2 CFSG.KC.BM.Five.f85_sq2 CFSG.KC.BM.Five.f86_sq1 CFSG.KC.BM.Five.f85_sq2 CFSG.KC.BM.Five.f86_sq1 CFSG.KC.BM.Five.f85_sq2 CFSG.KC.BM.Five.f86 CFSG.KC.BM.Five.f85 CFSG.KC.BM.Five.H3] n1 []
#bm_mul4 CFSG.KC.BM.FiveN cn2 CFSG.KC.BM.Five.oh_p [CFSG.KC.BM.Five.oh_p CFSG.KC.BM.Five.f85 CFSG.KC.BM.Five.oh_p CFSG.KC.BM.Five.f85 CFSG.KC.BM.Five.f86 CFSG.KC.BM.Five.f85] n2 []
#bm_mul4 CFSG.KC.BM.FiveN ce0 CFSG.KC.BM.Five.f85_sq2 [CFSG.KC.BM.Five.W_sq3 CFSG.KC.BM.Five.Q2_sq1 CFSG.KC.BM.Five.Q3_sq2 CFSG.KC.BM.Five.Q4_sq1 CFSG.KC.BM.Five.Q4 CFSG.KC.BM.Five.Zp3] e0 []
#bm_mul4 CFSG.KC.BM.FiveN ce1 CFSG.KC.BM.Five.f85_sq1 [CFSG.KC.BM.Five.W_sq3_sq2 CFSG.KC.BM.Five.Q2_sq2 CFSG.KC.BM.Five.Q3 CFSG.KC.BM.Five.Q4_sq1 CFSG.KC.BM.Five.Q4 CFSG.KC.BM.Five.Zp4] e1 []
#bm_mul4 CFSG.KC.BM.FiveN ce2 CFSG.KC.BM.Five.f85_sq2 [CFSG.KC.BM.Five.Q1e3 CFSG.KC.BM.Five.Q3_sq1 CFSG.KC.BM.Five.Q4_sq2 CFSG.KC.BM.Five.Z] e2 []
#bm_mul4 CFSG.KC.BM.FiveN cm0 n0 [CFSG.KC.BM.Five.f85] m0 []
#bm_mul4 CFSG.KC.BM.FiveN cm1 n1 [CFSG.KC.BM.Five.f85] m1 []
#bm_mul4 CFSG.KC.BM.FiveN cm2 n2 [CFSG.KC.BM.Five.f85] m2 []
#bm_mul4 CFSG.KC.BM.FiveN dm0 e0 [n0] m0 []
#bm_mul4 CFSG.KC.BM.FiveN dm1 e1 [n1] m1 []
#bm_mul4 CFSG.KC.BM.FiveN dm2 e2 [n2] m2 []
#bm_bool CFSG.KC.BM.FiveN wf_n0 (CFSG.KC.BM.wfMat n0)
#bm_bool CFSG.KC.BM.FiveN wf_n1 (CFSG.KC.BM.wfMat n1)
#bm_bool CFSG.KC.BM.FiveN wf_n2 (CFSG.KC.BM.wfMat n2)
#bm_bool CFSG.KC.BM.FiveN wf_e0 (CFSG.KC.BM.wfMat e0)
#bm_bool CFSG.KC.BM.FiveN wf_e1 (CFSG.KC.BM.wfMat e1)
#bm_bool CFSG.KC.BM.FiveN wf_e2 (CFSG.KC.BM.wfMat e2)
#bm_bool CFSG.KC.BM.FiveN wf_m0 (CFSG.KC.BM.wfMat m0)
#bm_bool CFSG.KC.BM.FiveN wf_m1 (CFSG.KC.BM.wfMat m1)
#bm_bool CFSG.KC.BM.FiveN wf_m2 (CFSG.KC.BM.wfMat m2)
