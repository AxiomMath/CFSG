module

import CFSG.Certificates.Kernel.BabyMonster.LoadFour
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.Fu.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Fu.Data1
public import CFSG.Certificates.Kernel.BabyMonster.Fu.Data2
public import CFSG.Certificates.Kernel.BabyMonster.Fu.Data3
public import CFSG.Certificates.Kernel.BabyMonster.Fu.Data4
public import CFSG.Certificates.Kernel.BabyMonster.Fu.Data5
public import CFSG.Certificates.Kernel.BabyMonster.Fu.Data13
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Data0

#bm_mul4 CFSG.KC.BM.Fu cw q0 [CFSG.KC.BM.Max2.r5 CFSG.KC.BM.Max2.r4] fws2 []
#bm_mul4 CFSG.KC.BM.Fu cfws4 fws2 [q2 q1] fws4 []
#bm_mul4 CFSG.KC.BM.Fu cfws6 fws4 [q2 q6] fws6 []
#bm_mul4 CFSG.KC.BM.Fu cfws8 fws6 [q14 CFSG.KC.BM.Max2.r5] fws8 []
#bm_mul4 CFSG.KC.BM.Fu cfws10 fws8 [q2 q4] fws10 []
#bm_mul4 CFSG.KC.BM.Fu cfws12 fws10 [q3 q4] fws12 []
#bm_mul4 CFSG.KC.BM.Fu cfws14 fws12 [q2 q2] fws14 []
#bm_mul4 CFSG.KC.BM.Fu cfws16 fws14 [q5 q1] fws16 []
#bm_mul4 CFSG.KC.BM.Fu cfws18 fws16 [q1 q14] fws18 []
#bm_mul4 CFSG.KC.BM.Fu cfws20 fws18 [q15 q5] fws20 []
#bm_mul4 CFSG.KC.BM.Fu cfws21 fws20 [q15] w []
#bm_bool CFSG.KC.BM.Fu wf_fws2 (CFSG.KC.BM.wfMat fws2)
#bm_bool CFSG.KC.BM.Fu wf_fws4 (CFSG.KC.BM.wfMat fws4)
#bm_bool CFSG.KC.BM.Fu wf_fws6 (CFSG.KC.BM.wfMat fws6)
#bm_bool CFSG.KC.BM.Fu wf_fws8 (CFSG.KC.BM.wfMat fws8)
#bm_bool CFSG.KC.BM.Fu wf_fws10 (CFSG.KC.BM.wfMat fws10)
#bm_bool CFSG.KC.BM.Fu wf_fws12 (CFSG.KC.BM.wfMat fws12)
#bm_bool CFSG.KC.BM.Fu wf_fws14 (CFSG.KC.BM.wfMat fws14)
#bm_bool CFSG.KC.BM.Fu wf_fws16 (CFSG.KC.BM.wfMat fws16)
#bm_bool CFSG.KC.BM.Fu wf_fws18 (CFSG.KC.BM.wfMat fws18)
#bm_bool CFSG.KC.BM.Fu wf_fws20 (CFSG.KC.BM.wfMat fws20)
