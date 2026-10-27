module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data3
public import CFSG.Certificates.Kernel.BabyMonster.SevenGen.Data3
public import CFSG.Certificates.Kernel.BabyMonster.SevenGen.Data4
public import CFSG.Certificates.Kernel.BabyMonster.SevenGen.Data5

#bm_mul CFSG.KC.BM.SevenGen c_c di [q d] c []
#bm_bool CFSG.KC.BM.SevenGen wf_c (CFSG.KC.BM.wfMat c)
#bm_mul CFSG.KC.BM.SevenGen c_ci c [ci] I []
#bm_bool CFSG.KC.BM.SevenGen wf_ci (CFSG.KC.BM.wfMat ci)
#bm_mul CFSG.KC.BM.SevenGen c_s2 ci [CFSG.KC.BM.Seven.g c] s2 []
#bm_bool CFSG.KC.BM.SevenGen wf_s2 (CFSG.KC.BM.wfMat s2)
#bm_mul CFSG.KC.BM.SevenGen c_gi CFSG.KC.BM.Seven.g [gi] I []
#bm_bool CFSG.KC.BM.SevenGen wf_gi (CFSG.KC.BM.wfMat gi)
#bm_mul CFSG.KC.BM.SevenGen c_s2i s2 [s2i] I []
#bm_bool CFSG.KC.BM.SevenGen wf_s2i (CFSG.KC.BM.wfMat s2i)
