module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data3
public import CFSG.Certificates.Kernel.BabyMonster.SevenGen.Data5
public import CFSG.Certificates.Kernel.BabyMonster.SevenGen.Spin

#bm_bool CFSG.KC.BM.SevenGen wf_vf (CFSG.KC.BM.onlyRows vf 1)
#bm_bool CFSG.KC.BM.SevenGen fix_x (Nat.beq (CFSG.KC.BM.mulS CFSG.KC.BM.Seven.x vf) vf)
#bm_bool CFSG.KC.BM.SevenGen move_f (CFSG.KC.BM.notB (Nat.beq (CFSG.KC.BM.rowOf (CFSG.KC.BM.mulS f vf) 0) (CFSG.KC.BM.rowOf vf 0)))
