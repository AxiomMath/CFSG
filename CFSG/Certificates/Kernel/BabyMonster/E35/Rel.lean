module

import CFSG.Certificates.Kernel.BabyMonster.Load
import CFSG.Certificates.Kernel.BabyMonster.LoadFour
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import CFSG.Certificates.Kernel.BabyMonster.E35.Data2
public import CFSG.Certificates.Kernel.BabyMonster.E35.Data3

#bm_mul4 CFSG.KC.BM.E35 ord_x x2 [x] I []
#bm_mul4 CFSG.KC.BM.E35 ord_z z [z] I []
#bm_mul4 CFSG.KC.BM.E35 cm_zx z [x] x [z]
#bm_mul4 CFSG.KC.BM.E35 cm_x1 x [x1] x1 [x]
#bm_mul4 CFSG.KC.BM.E35 cm_y2 x [y2] y2 [x]
#bm_bool CFSG.KC.BM.E35 ne_z (CFSG.KC.BM.notB (CFSG.KC.BM.isId z))
#bm_bool CFSG.KC.BM.E35 ne_x1 (CFSG.KC.BM.notB (CFSG.KC.BM.eqMat x1 x))
#bm_bool CFSG.KC.BM.E35 ne_P (CFSG.KC.BM.notB (Nat.beq (CFSG.KC.BM.rowOf (CFSG.KC.BM.mulW (L2 x gi x gi x gi x gi x g4) 1) 0) (CFSG.KC.BM.rowOf 1 0)))
