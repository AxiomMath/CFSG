module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Data0
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Data1
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Data2
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Data3
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Data4
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Data5
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Data6
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Data7
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Data8
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Data9
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Data10
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Data11
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Data12
public import CFSG.Certificates.Kernel.BabyMonster.B9201.Data0
public import CFSG.Certificates.Kernel.BabyMonster.B9201.Data1
public import CFSG.Certificates.Kernel.BabyMonster.B9201.Data2
public import CFSG.Certificates.Kernel.BabyMonster.B9201.Spin
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0

#bm_mul CFSG.KC.BM.B9201 c_h2 sr [sr] h2 []
#bm_mul CFSG.KC.BM.B9201 c_h4 h2 [h2] h4 []
#bm_mul CFSG.KC.BM.B9201 c_h5 h4 [sr] h5 []
#bm_mul CFSG.KC.BM.B9201 c_h h5 [h5] h []
#bm_mul CFSG.KC.BM.B9201 c_K Gp [h] K []
#bm_bool CFSG.KC.BM.B9201 wf_Gp (CFSG.KC.BM.wfMat Gp)
#bm_bool CFSG.KC.BM.B9201 wf_Gip (CFSG.KC.BM.wfMat Gip)
#bm_mul CFSG.KC.BM.B9201 t1sq CFSG.KC.BM.BProg.t1 [CFSG.KC.BM.BProg.t1] I []
#bm_mul CFSG.KC.BM.B9201 braid12 r2 [r2 r2] I []
#bm_mul CFSG.KC.BM.B9201 com1_3 CFSG.KC.BM.BProg.t1 [CFSG.KC.BM.BProg.t3] CFSG.KC.BM.BProg.t3 [CFSG.KC.BM.BProg.t1]
#bm_mul CFSG.KC.BM.B9201 com1_4 CFSG.KC.BM.BProg.t1 [CFSG.KC.BM.BProg.t4] CFSG.KC.BM.BProg.t4 [CFSG.KC.BM.BProg.t1]
