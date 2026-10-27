module

import CFSG.Certificates.Kernel.BabyMonster.Load
import CFSG.Certificates.Kernel.BabyMonster.LoadFour
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import CFSG.Certificates.Kernel.BabyMonster.Render
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Data2
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Data4
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Data5
public import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data0
public import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data1
public import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data2
public import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data3
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Max2Br.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Max2Br.Data1
public import CFSG.Certificates.Kernel.BabyMonster.Max2Br.Data2
public import CFSG.Certificates.Kernel.BabyMonster.Max2T.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Max2T.Data1
public import CFSG.Certificates.Kernel.BabyMonster.Max2T.Vecs

#bm_mul4 CFSG.KC.BM.Max2T cYz_sq1 Yz [Yz] Yz_sq1 []
#bm_mul4 CFSG.KC.BM.Max2T cYz_sq2 Yz_sq1 [Yz_sq1] Yz_sq2 []
#bm_mul4 CFSG.KC.BM.Max2T oy_pow Yz_sq2 [Yz] I []
#bm_bool CFSG.KC.BM.Max2T oy_orb (CFSG.KC.BM.andB (CFSG.KC.BM.andB (CFSG.KC.BM.onlyRows Voy 5) (Nat.beq (CFSG.KC.BM.rowsBlk Voy 0 1) 1)) (CFSG.KC.BM.andB (Nat.beq (CFSG.KC.BM.rowsBlk Voy 1 4) (CFSG.KC.BM.rowsBlk (CFSG.KC.BM.mulS Yz Voy) 0 4)) (CFSG.KC.BM.allDistinct (CFSG.KC.BM.rowList [Voy] 5))))
