module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.Max5.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Max5.Data1
public import CFSG.Certificates.Kernel.BabyMonster.Max5.Data2
public import CFSG.Certificates.Kernel.BabyMonster.MultSeven.Data0
public import CFSG.Certificates.Kernel.BabyMonster.MultSeven.Data1
public import CFSG.Certificates.Kernel.BabyMonster.MultSeven.Data2
public import CFSG.Certificates.Kernel.BabyMonster.MultSeven.Vecs
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0

#bm_mul CFSG.KC.BM.MultSeven sq_act x4 [y2 h3 y] h3 []
#bm_bool CFSG.KC.BM.MultSeven sq_orb (CFSG.KC.BM.andB (CFSG.KC.BM.andB (CFSG.KC.BM.andB (CFSG.KC.BM.andB (CFSG.KC.BM.andB (CFSG.KC.BM.andB (CFSG.KC.BM.andB (CFSG.KC.BM.andB (CFSG.KC.BM.andB (CFSG.KC.BM.andB (CFSG.KC.BM.andB (CFSG.KC.BM.andB (CFSG.KC.BM.andB (CFSG.KC.BM.andB (CFSG.KC.BM.andB (CFSG.KC.BM.onlyRows V0 7) (Nat.beq (CFSG.KC.BM.rowsBlk V0 0 1) 1)) (Nat.beq (CFSG.KC.BM.rowsBlk V0 1 6) (CFSG.KC.BM.rowsBlk (CFSG.KC.BM.mulS x V0) 0 6))) (CFSG.KC.BM.onlyRows V1 7)) (Nat.beq V1 (CFSG.KC.BM.mulS y V0))) (CFSG.KC.BM.onlyRows V2 7)) (Nat.beq V2 (CFSG.KC.BM.mulS y V1))) (CFSG.KC.BM.onlyRows V3 7)) (Nat.beq V3 (CFSG.KC.BM.mulS y V2))) (CFSG.KC.BM.onlyRows V4 7)) (Nat.beq V4 (CFSG.KC.BM.mulS y V3))) (CFSG.KC.BM.onlyRows V5 7)) (Nat.beq V5 (CFSG.KC.BM.mulS y V4))) (CFSG.KC.BM.onlyRows V6 7)) (Nat.beq V6 (CFSG.KC.BM.mulS y V5))) (CFSG.KC.BM.allDistinct (CFSG.KC.BM.rowList [V0 V1 V2 V3 V4 V5 V6] 7)))
