module

public import CFSG.Certificates.Kernel.YModel.Y321.Data
public import CFSG.YGroups.Defs
import CFSG.Certificates.Kernel.Common.Each
public import Mathlib

public section

set_option maxRecDepth 100000

namespace CFSG.KD.YMY321

open CFSG.KC CFSG.KC.YModel CFSG.YGroups

@[expose] noncomputable def ch10097let (c : Nat) : Bool :=
  andB (letOK 6 56 (CFSG.KD.YM321P.F c) (Nf c)) (Nat.beq (lget CFSG.KD.YM321P.El c) 56)

@[expose] noncomputable def ch10097lev (i : Nat) : Bool :=
  levelOK 6 56 7 T0 (CFSG.KD.YM321C.F 0) R0 M0 Z0 i

#kc_each ch10097let 0 7
#kc_each ch10097lev 0 6

theorem ch10097rels : relsOK 6 7 Nf (yRels 3 2 1) = true := by
  quickRfl

@[expose] noncomputable def ch10097cut (i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (M0 i) (Nat.xor (M0 0) (Nat.shiftLeft 1 5)) (Nat.beq i 0)

theorem ch10097neg :
    (!letOK 6 56 (CFSG.KD.YM321P.F 0) (Nf 1) &&
      !relsOK 6 7 Nf [[0, 1, 0, 1]] &&
      !levelOK 6 56 7 T0 (CFSG.KD.YM321C.F 0) R0 ch10097cut Z0 0 &&
      !levelOK 6 56 7 T0 (CFSG.KD.YM321C.F 0) R0 M0 (fun i => Nat.succ (Z0 i)) 2) = true := by
  quickRfl

end CFSG.KD.YMY321

end
