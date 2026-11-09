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

#bm_mul4 CFSG.KC.BM.FiveN cn2 CFSG.KC.BM.Five.oh_p [CFSG.KC.BM.Five.oh_p CFSG.KC.BM.Five.f85] n2a []
#bm_mul4 CFSG.KC.BM.FiveN cn2b n2a [CFSG.KC.BM.Five.oh_p CFSG.KC.BM.Five.f85] n2b []
#bm_mul4 CFSG.KC.BM.FiveN cn2c n2b [CFSG.KC.BM.Five.f86 CFSG.KC.BM.Five.f85] n2 []
#bm_mul4 CFSG.KC.BM.FiveN ce2 CFSG.KC.BM.Five.f85_sq2 [CFSG.KC.BM.Five.Q1e3 CFSG.KC.BM.Five.Q3_sq1] e2a []
#bm_mul4 CFSG.KC.BM.FiveN ce2b e2a [CFSG.KC.BM.Five.Q4_sq2 CFSG.KC.BM.Five.Z] e2 []
#bm_mul4 CFSG.KC.BM.FiveN cm2 n2 [CFSG.KC.BM.Five.f85] m2 []
#bm_mul4 CFSG.KC.BM.FiveN dm1 e1 [n1] m1 []
#bm_mul4 CFSG.KC.BM.FiveN dm2 e2 [n2] m2 []
#bm_bool CFSG.KC.BM.FiveN wf_n2a (CFSG.KC.BM.wfMat n2a)
#bm_bool CFSG.KC.BM.FiveN wf_n2b (CFSG.KC.BM.wfMat n2b)
#bm_bool CFSG.KC.BM.FiveN wf_e2a (CFSG.KC.BM.wfMat e2a)
#bm_bool CFSG.KC.BM.FiveN wf_n2 (CFSG.KC.BM.wfMat n2)
#bm_bool CFSG.KC.BM.FiveN wf_e2 (CFSG.KC.BM.wfMat e2)
#bm_bool CFSG.KC.BM.FiveN wf_m2 (CFSG.KC.BM.wfMat m2)
