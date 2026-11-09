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

#bm_mul4 CFSG.KC.BM.FiveN cn1 CFSG.KC.BM.Five.f86 [CFSG.KC.BM.Five.f85_sq2 CFSG.KC.BM.Five.f85_sq2] n1a []
#bm_mul4 CFSG.KC.BM.FiveN cn1b n1a [CFSG.KC.BM.Five.f86_sq1 CFSG.KC.BM.Five.f85_sq2] n1b []
#bm_mul4 CFSG.KC.BM.FiveN cn1c n1b [CFSG.KC.BM.Five.f86_sq1 CFSG.KC.BM.Five.f85_sq2] n1c []
#bm_mul4 CFSG.KC.BM.FiveN cn1d n1c [CFSG.KC.BM.Five.f86 CFSG.KC.BM.Five.f85] n1d []
#bm_mul4 CFSG.KC.BM.FiveN cn1e n1d [CFSG.KC.BM.Five.H3] n1 []
#bm_mul4 CFSG.KC.BM.FiveN ce1 CFSG.KC.BM.Five.f85_sq1 [CFSG.KC.BM.Five.W_sq3_sq2 CFSG.KC.BM.Five.Q2_sq2] e1a []
#bm_mul4 CFSG.KC.BM.FiveN ce1b e1a [CFSG.KC.BM.Five.Q3 CFSG.KC.BM.Five.Q4_sq1] e1b []
#bm_mul4 CFSG.KC.BM.FiveN ce1c e1b [CFSG.KC.BM.Five.Q4 CFSG.KC.BM.Five.Zp4] e1 []
#bm_bool CFSG.KC.BM.FiveN wf_n1a (CFSG.KC.BM.wfMat n1a)
#bm_bool CFSG.KC.BM.FiveN wf_n1b (CFSG.KC.BM.wfMat n1b)
#bm_bool CFSG.KC.BM.FiveN wf_n1c (CFSG.KC.BM.wfMat n1c)
#bm_bool CFSG.KC.BM.FiveN wf_n1d (CFSG.KC.BM.wfMat n1d)
#bm_bool CFSG.KC.BM.FiveN wf_e1a (CFSG.KC.BM.wfMat e1a)
#bm_bool CFSG.KC.BM.FiveN wf_e1b (CFSG.KC.BM.wfMat e1b)
#bm_bool CFSG.KC.BM.FiveN wf_n1 (CFSG.KC.BM.wfMat n1)
#bm_bool CFSG.KC.BM.FiveN wf_e1 (CFSG.KC.BM.wfMat e1)
#bm_bool CFSG.KC.BM.FiveN wf_m1 (CFSG.KC.BM.wfMat m1)
