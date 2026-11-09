module

import CFSG.Certificates.Kernel.BabyMonster.Load
import CFSG.Certificates.Kernel.BabyMonster.LoadFour
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data3
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data4
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data9
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data10
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data11
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data12
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data13
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data14
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data15
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data16
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data17
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data18
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data19
public import CFSG.Certificates.Kernel.BabyMonster.FiveN.Data0

#bm_mul4 CFSG.KC.BM.FiveN cn0 CFSG.KC.BM.Five.f86 [CFSG.KC.BM.Five.f85_sq2 CFSG.KC.BM.Five.f86_sq1] n0a []
#bm_mul4 CFSG.KC.BM.FiveN cn0b n0a [CFSG.KC.BM.Five.f85_sq2 CFSG.KC.BM.Five.f85_sq2] n0b []
#bm_mul4 CFSG.KC.BM.FiveN cn0c n0b [CFSG.KC.BM.Five.f86 CFSG.KC.BM.Five.f85_sq2] n0 []
#bm_mul4 CFSG.KC.BM.FiveN ce0 CFSG.KC.BM.Five.f85_sq2 [CFSG.KC.BM.Five.W_sq3 CFSG.KC.BM.Five.Q2_sq1] e0a []
#bm_mul4 CFSG.KC.BM.FiveN ce0b e0a [CFSG.KC.BM.Five.Q3_sq2 CFSG.KC.BM.Five.Q4_sq1] e0b []
#bm_mul4 CFSG.KC.BM.FiveN ce0c e0b [CFSG.KC.BM.Five.Q4 CFSG.KC.BM.Five.Zp3] e0 []
#bm_mul4 CFSG.KC.BM.FiveN cm0 n0 [CFSG.KC.BM.Five.f85] m0 []
#bm_mul4 CFSG.KC.BM.FiveN dm0 e0 [n0] m0 []
#bm_mul4 CFSG.KC.BM.FiveN cm1 n1 [CFSG.KC.BM.Five.f85] m1 []
#bm_bool CFSG.KC.BM.FiveN wf_n0a (CFSG.KC.BM.wfMat n0a)
#bm_bool CFSG.KC.BM.FiveN wf_n0b (CFSG.KC.BM.wfMat n0b)
#bm_bool CFSG.KC.BM.FiveN wf_e0a (CFSG.KC.BM.wfMat e0a)
#bm_bool CFSG.KC.BM.FiveN wf_e0b (CFSG.KC.BM.wfMat e0b)
#bm_bool CFSG.KC.BM.FiveN wf_n0 (CFSG.KC.BM.wfMat n0)
#bm_bool CFSG.KC.BM.FiveN wf_e0 (CFSG.KC.BM.wfMat e0)
#bm_bool CFSG.KC.BM.FiveN wf_m0 (CFSG.KC.BM.wfMat m0)
