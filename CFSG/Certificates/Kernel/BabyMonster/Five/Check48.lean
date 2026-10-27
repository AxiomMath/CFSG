module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data1
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data2
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data3
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data4
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data5
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data6
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data7
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data8
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data9
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data10
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data11
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data12
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data13
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data14
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data15
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data16
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data17
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data18
public import CFSG.Certificates.Kernel.BabyMonster.Five.Data19
public import CFSG.Certificates.Kernel.BabyMonster.Five.Vecs
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0

#bm_mul CFSG.KC.BM.Five cZ_sq1 Z [Z] Z_sq1 []
#bm_mul CFSG.KC.BM.Five cZ_sq2 Z_sq1 [Z_sq1] Z_sq2 []
#bm_mul CFSG.KC.BM.Five oz_pow Z_sq2 [Z] I []
#bm_bool CFSG.KC.BM.Five oz_orb (CFSG.KC.BM.andB (CFSG.KC.BM.andB (CFSG.KC.BM.onlyRows Voz 5) (Nat.beq (CFSG.KC.BM.rowsBlk Voz 0 1) 1)) (CFSG.KC.BM.andB (Nat.beq (CFSG.KC.BM.rowsBlk Voz 1 4) (CFSG.KC.BM.rowsBlk (CFSG.KC.BM.mulS Z Voz) 0 4)) (CFSG.KC.BM.allDistinct (CFSG.KC.BM.rowList [Voz] 5))))
