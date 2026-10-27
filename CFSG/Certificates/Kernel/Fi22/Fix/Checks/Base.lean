module

public import CFSG.Certificates.Kernel.Fi22.Fix.Sel
public import CFSG.Certificates.Kernel.Fi22.Bound.Data.P_Sel
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Fi22.Fix.Defs

public noncomputable section

namespace CFSG.KD.Fi22F

open CFSG.KC.Fi22F

@[expose] def Rsel (c : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) R3 R2 (Nat.beq c 2))
      R1 (Nat.beq c 1))
    R0 (Nat.beq c 0)

@[expose] def rg (c : Nat) : Bool := rangeOK (Lsel c)

@[expose] def «let» (c : Nat) : Bool := letOK CFSG.KD.Fi22BP.blk 82571 LV (Lsel c) (Rsel c) c

theorem lv0 : Nat.beq (lv LV 0) 0 = true := by quickRfl

theorem idI : idOK I = true := by quickRfl

end CFSG.KD.Fi22F

#kc_each CFSG.KD.Fi22F.rg 0 4
#kc_each CFSG.KD.Fi22F.«let» 0 4

end
