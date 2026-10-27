module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data3
public import CFSG.Certificates.Kernel.BabyMonster.SevenGen.Data3
public import CFSG.Certificates.Kernel.BabyMonster.SevenGen.Data5

#bm_mul CFSG.KC.BM.SevenGen c_ap apw [r88] ap []
#bm_bool CFSG.KC.BM.SevenGen wf_ap (CFSG.KC.BM.wfMat ap)
#bm_mul CFSG.KC.BM.SevenGen c_s2sq s2 [s2] s2sq []
#bm_bool CFSG.KC.BM.SevenGen wf_s2sq (CFSG.KC.BM.wfMat s2sq)
#bm_mul CFSG.KC.BM.SevenGen c_bpw CFSG.KC.BM.Seven.g [s2 gi s2sq] bpw []
#bm_bool CFSG.KC.BM.SevenGen wf_bpw (CFSG.KC.BM.wfMat bpw)
#bm_mul CFSG.KC.BM.SevenGen c_r89 bpw [bpw] r89 []
#bm_bool CFSG.KC.BM.SevenGen wf_r89 (CFSG.KC.BM.wfMat r89)
#bm_mul CFSG.KC.BM.SevenGen c_r90 r89 [r89] r90 []
#bm_bool CFSG.KC.BM.SevenGen wf_r90 (CFSG.KC.BM.wfMat r90)
