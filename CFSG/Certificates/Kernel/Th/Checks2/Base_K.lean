module

public import CFSG.Certificates.Kernel.Th.S.BaseS
public import CFSG.Certificates.Kernel.Th.S.BigS
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.Certificates.Kernel.Th.S.Data.Seed_const
public import CFSG.Certificates.Kernel.Th.S.Data.Base_const
public import Certificates.Data.CFSGNative.Th.FormCheck
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Th.S.SeedS

public section

namespace CFSG.KC.Th.BaseK

open CFSG.KC.Th CFSG.KC.Th.BaseS CFSG.KD.ThS

theorem pack_C : SeedS.packOK CFSG.KD.ThBase.C deltaRows = true := by quickRfl

theorem gram : Nat.beq (mulB c rm (mulB c rm CFSG.KD.ThBase.C CFSG.KD.ThSeed.SF)
    (trB tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 CFSG.KD.ThBase.C)) CFSG.KD.ThBase.G = true := by quickRfl

theorem inv_C : Nat.beq (mulB c rm CFSG.KD.ThBase.N CFSG.KD.ThBase.C) ONE = true := by quickRfl

theorem form_base : CFSG.Sporadic.Th.formBaseCheck 124 (blkG rm CFSG.KD.ThBase.G) = true := by
  quickRfl

theorem pack_C_neg :
    BigS.notB (SeedS.packOK (Nat.xor CFSG.KD.ThBase.C 1) deltaRows) = true := by quickRfl

theorem gram_neg : BigS.notB (Nat.beq (mulB c rm (mulB c rm CFSG.KD.ThBase.C CFSG.KD.ThSeed.SF)
    (trB tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 CFSG.KD.ThBase.C)) (Nat.xor CFSG.KD.ThBase.G 2)) = true := by
  quickRfl

theorem inv_C_neg :
    BigS.notB (Nat.beq (mulB c rm (Nat.xor CFSG.KD.ThBase.N 1) CFSG.KD.ThBase.C) ONE) = true := by
  quickRfl

theorem form_base_neg : BigS.notB (CFSG.Sporadic.Th.formBaseCheck 124 fun _ _ => 9) = true := by
  quickRfl

end CFSG.KC.Th.BaseK

end
