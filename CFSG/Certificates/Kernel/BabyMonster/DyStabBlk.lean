module

public import CFSG.Certificates.Kernel.BabyMonster.LatCheck
public import CFSG.Certificates.Kernel.BabyMonster.Native.Dyadic
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.KC.BM.Dy

open CFSG.KC.BM CFSG.KC.BM.Lat

@[expose] noncomputable def rowsNeR (C : List (List Nat)) (X lo : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun l ih => andB ih (andB (Nat.blt (recOf C (Nat.add lo l)) dyFail)
      (notB (Nat.beq (recOf C (Nat.add lo l)) X))))

@[expose] noncomputable def rowsNeB (C : List (List Nat)) (X b : Nat) : Bool :=
  rowsNeR C X (Nat.mul (nat_lit 64) b) (nat_lit 64)

end CFSG.KC.BM.Dy

end
