module

import CFSG.Certificates.Kernel.BabyMonster.Load
import CFSG.Certificates.Kernel.BabyMonster.LoadFour
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data5
public import CFSG.Certificates.Kernel.BabyMonster.SevenGen.Spin
public import CFSG.Certificates.Kernel.BabyMonster.SevenLocal.Data1
public import CFSG.Certificates.Kernel.BabyMonster.SevenLocal.Data2

#bm_mul4 CFSG.KC.BM.SevenLocal cm_ft1 f [CFSG.KC.BM.Seven.t1] CFSG.KC.BM.Seven.t1 [f]
#bm_mul4 CFSG.KC.BM.SevenLocal ord_u1 u1p2 [u1] I []
#bm_mul4 CFSG.KC.BM.SevenLocal ord_u2 u2p2 [u2] I []
#bm_mul4 CFSG.KC.BM.SevenLocal cm_u2u1 u2 [u1] u12 []
#bm_bool CFSG.KC.BM.SevenLocal ne_ts3 (CFSG.KC.BM.notB (CFSG.KC.BM.isId ts3))
#bm_bool CFSG.KC.BM.SevenLocal ne_f (CFSG.KC.BM.notB (CFSG.KC.BM.isId f))
#bm_bool CFSG.KC.BM.SevenLocal move_f (CFSG.KC.BM.notB (Nat.beq (CFSG.KC.BM.rowOf (CFSG.KC.BM.mulS f CFSG.KC.BM.SevenGen.vf) 0) (CFSG.KC.BM.rowOf CFSG.KC.BM.SevenGen.vf 0)))
#bm_bool CFSG.KC.BM.SevenLocal ne_u2_u1 (CFSG.KC.BM.notB (CFSG.KC.BM.eqMat u2 u1))
#bm_bool CFSG.KC.BM.SevenLocal ne_u2_u1p2 (CFSG.KC.BM.notB (CFSG.KC.BM.eqMat u2 u1p2))
