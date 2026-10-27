module

import CFSG.Certificates.Kernel.BabyMonster.LoadFour
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import CFSG.Certificates.Kernel.BabyMonster.E35.Data2

#bm_mul4 CFSG.KC.BM.E35 c_wg2 wg [wg] wg2 []
#bm_mul4 CFSG.KC.BM.E35 c_g wg2 [wg] g []
#bm_mul4 CFSG.KC.BM.E35 c_g2 g [g] g2 []
#bm_mul4 CFSG.KC.BM.E35 c_g4 g2 [g2] g4 []
#bm_mul4 CFSG.KC.BM.E35 c_z g4 [g] z []
#bm_mul4 CFSG.KC.BM.E35 c_gi z [g4] gi []
