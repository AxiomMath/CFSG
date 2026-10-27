module

public import CFSG.Sporadic.Schreier.Co1ChainCheck
public import Certificates.Data.Kernel.Spor.Raw
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.KS.SporSch.Lift

open CFSG.Sporadic.Co1Schreier.Native CFSG.KS.Raw

@[expose] def clsValS (R : Array Nat) (z m : Nat) : Nat :=
  if m < 2300 then R[m]! else z ^^^ R[m - 2300]!

@[expose] def inClsS (R : Array Nat) (z w k : Nat) : Bool :=
  w == clsValS R z k || w == clsValS R z (k + 2300)

@[expose] def liftSpec (R a0 a1 H0 H1 : Array Nat) (z : Nat) : Bool :=
  R.size == 2300 &&
    (List.range 4600).all (fun m => decide (clsValS R z m < 2 ^ 24)) &&
    vSorted (((List.range 4600).map (clsValS R z)).mergeSort fun a b => decide (a ≤ b)) &&
    (List.range 2300).all fun j =>
      inClsS R z (act H0 R[j]!) a0[j]! && inClsS R z (act H1 R[j]!) a1[j]!

end CFSG.KS.SporSch.Lift

end
