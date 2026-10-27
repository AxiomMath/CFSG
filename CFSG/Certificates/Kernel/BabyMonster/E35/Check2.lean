module

import CFSG.Certificates.Kernel.BabyMonster.LoadFour
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import CFSG.Certificates.Kernel.BabyMonster.E35.Data0
public import CFSG.Certificates.Kernel.BabyMonster.E35.Data1
public import CFSG.Certificates.Kernel.BabyMonster.E35.Data2

#bm_mul4 CFSG.KC.BM.E35 c_p h1 [h2] p []
#bm_mul4 CFSG.KC.BM.E35 c_q p [h2] q []
#bm_mul4 CFSG.KC.BM.E35 c_pp p [p] pp []
#bm_mul4 CFSG.KC.BM.E35 c_ppq pp [q] ppq []
#bm_mul4 CFSG.KC.BM.E35 c_ppqq ppq [q] ppqq []
#bm_mul4 CFSG.KC.BM.E35 c_wg ppqq [q] wg []
