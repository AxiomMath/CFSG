module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data3
public import CFSG.Certificates.Kernel.BabyMonster.SevenGen.Data5

#bm_mul CFSG.KC.BM.SevenGen c_r100 s2i [CFSG.KC.BM.Seven.g] r100 []
#bm_bool CFSG.KC.BM.SevenGen wf_r100 (CFSG.KC.BM.wfMat r100)
#bm_mul CFSG.KC.BM.SevenGen c_apw CFSG.KC.BM.Seven.r32 [r100 r100] apw []
#bm_bool CFSG.KC.BM.SevenGen wf_apw (CFSG.KC.BM.wfMat apw)
#bm_mul CFSG.KC.BM.SevenGen c_r85 apw [apw] r85 []
#bm_bool CFSG.KC.BM.SevenGen wf_r85 (CFSG.KC.BM.wfMat r85)
#bm_mul CFSG.KC.BM.SevenGen c_r86 r85 [r85] r86 []
#bm_bool CFSG.KC.BM.SevenGen wf_r86 (CFSG.KC.BM.wfMat r86)
#bm_mul CFSG.KC.BM.SevenGen c_r87 r86 [r86] r87 []
#bm_bool CFSG.KC.BM.SevenGen wf_r87 (CFSG.KC.BM.wfMat r87)
#bm_mul CFSG.KC.BM.SevenGen c_r88 r87 [r87] r88 []
#bm_bool CFSG.KC.BM.SevenGen wf_r88 (CFSG.KC.BM.wfMat r88)
