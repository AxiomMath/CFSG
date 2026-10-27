module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data5
public import CFSG.Certificates.Kernel.BabyMonster.Fi23.Data12
public import CFSG.Certificates.Kernel.BabyMonster.Fi23R.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Fi23R.Data1

#bm_mul CFSG.KC.BM.Fi23R cw1sq w1 [w1] w1sq []
#bm_mul CFSG.KC.BM.Fi23R cw1p5 w1sq [w1sq w1] w1p5 []
#bm_mul CFSG.KC.BM.Fi23R w1p10 w1p5 [w1p5] I []
#bm_mul CFSG.KC.BM.Fi23R cw2 e01 [e23 e45 CFSG.KC.BM.Fi23.img7] w2 []
#bm_mul CFSG.KC.BM.Fi23R cw2p3 w2 [w2 w2] w2p3 []
#bm_mul CFSG.KC.BM.Fi23R w2p9 w2p3 [w2p3 w2p3] I []
#bm_bool CFSG.KC.BM.Fi23R ne_img0 (CFSG.KC.BM.notB (CFSG.KC.BM.isId CFSG.KC.BM.Fi23.img0))
#bm_bool CFSG.KC.BM.Fi23R wf_e01 (CFSG.KC.BM.wfMat e01)
#bm_bool CFSG.KC.BM.Fi23R wf_e12 (CFSG.KC.BM.wfMat e12)
#bm_bool CFSG.KC.BM.Fi23R wf_e23 (CFSG.KC.BM.wfMat e23)
#bm_bool CFSG.KC.BM.Fi23R wf_e34 (CFSG.KC.BM.wfMat e34)
#bm_bool CFSG.KC.BM.Fi23R wf_e45 (CFSG.KC.BM.wfMat e45)
#bm_bool CFSG.KC.BM.Fi23R wf_e56 (CFSG.KC.BM.wfMat e56)
#bm_bool CFSG.KC.BM.Fi23R wf_e69 (CFSG.KC.BM.wfMat e69)
#bm_bool CFSG.KC.BM.Fi23R wf_e37 (CFSG.KC.BM.wfMat e37)
#bm_bool CFSG.KC.BM.Fi23R wf_e78 (CFSG.KC.BM.wfMat e78)
#bm_bool CFSG.KC.BM.Fi23R wf_w1 (CFSG.KC.BM.wfMat w1)
#bm_bool CFSG.KC.BM.Fi23R wf_w1sq (CFSG.KC.BM.wfMat w1sq)
#bm_bool CFSG.KC.BM.Fi23R wf_w1p5 (CFSG.KC.BM.wfMat w1p5)
#bm_bool CFSG.KC.BM.Fi23R wf_w2 (CFSG.KC.BM.wfMat w2)
#bm_bool CFSG.KC.BM.Fi23R wf_w2p3 (CFSG.KC.BM.wfMat w2p3)
