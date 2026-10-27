module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.Three.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Three.Data1
public import CFSG.Certificates.Kernel.BabyMonster.Three.Data2
public import CFSG.Certificates.Kernel.BabyMonster.Three.Data3
public import CFSG.Certificates.Kernel.BabyMonster.Three.Data4
public import CFSG.Certificates.Kernel.BabyMonster.Three.Data5
public import CFSG.Certificates.Kernel.BabyMonster.Three.Data6
public import CFSG.Certificates.Kernel.BabyMonster.Three.Data7
public import CFSG.Certificates.Kernel.BabyMonster.Three.Data8
public import CFSG.Certificates.Kernel.BabyMonster.Three.Data9
public import CFSG.Certificates.Kernel.BabyMonster.Three.Data10
public import CFSG.Certificates.Kernel.BabyMonster.Three.Data11
public import CFSG.Certificates.Kernel.BabyMonster.Three.Data12
public import CFSG.Certificates.Kernel.BabyMonster.Three.Data13
public import CFSG.Certificates.Kernel.BabyMonster.Three.Data14
public import CFSG.Certificates.Kernel.BabyMonster.Three.Data15
public import CFSG.Certificates.Kernel.BabyMonster.Three.Data16
public import CFSG.Certificates.Kernel.BabyMonster.Three.Data17
public import CFSG.Certificates.Kernel.BabyMonster.Three.Data18
public import CFSG.Certificates.Kernel.BabyMonster.Three.Data19
public import CFSG.Certificates.Kernel.BabyMonster.Three.Data20
public import CFSG.Certificates.Kernel.BabyMonster.Three.Vecs
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0

#bm_mul CFSG.KC.BM.Three ct58_sq2 t58_sq1 [t58_sq1] t58_sq2 []
#bm_mul CFSG.KC.BM.Three coh_p oh_pp0 [t58_sq2] oh_p []
#bm_mul CFSG.KC.BM.Three oh_pow oh_p [t58] I []
#bm_bool CFSG.KC.BM.Three oh_orb (CFSG.KC.BM.andB (CFSG.KC.BM.andB (CFSG.KC.BM.onlyRows Voh 8) (Nat.beq (CFSG.KC.BM.rowsBlk Voh 0 1) 1)) (CFSG.KC.BM.andB (Nat.beq (CFSG.KC.BM.rowsBlk Voh 1 7) (CFSG.KC.BM.rowsBlk (CFSG.KC.BM.mulS t58 Voh) 0 7)) (CFSG.KC.BM.allDistinct (CFSG.KC.BM.rowList [Voh] 8))))
