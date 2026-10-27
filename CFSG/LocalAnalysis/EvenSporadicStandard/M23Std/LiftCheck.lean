module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.FusionCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.NoLift4

public section

namespace CFSG.EvenSporadicStandard.M23Std.LiftCheck

open CFSG.EvenSporadicStandard.Wong77.M23Sylow CFSG.EvenSporadicStandard.M23Std.FusionCheck

@[expose] def basisIdx : List Nat := [0, 1, 2, 4]

@[expose] def fTab (i : Nat) : Tab := (elemTabs 1).getD (basisIdx.getD i 0) idTab

@[expose] def powTab (t : Tab) : Nat → Tab
  | 0 => idTab
  | n + 1 => tmul t (powTab t n)

@[expose] def monoTab (ts : Fin 4 → Tab) (c : Fin 4 → ZMod 2) : Tab :=
  tmul (tmul (tmul (powTab (ts 0) (c 0).val) (powTab (ts 1) (c 1).val))
    (powTab (ts 2) (c 2).val)) (powTab (ts 3) (c 3).val)

@[expose] def b1Word : List Nat :=
  [
    2, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 2, 0, 2, 0, 2,
    0, 1, 0, 2, 2, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 1, 0,
    2, 0, 1, 0, 1, 0, 1, 0
  ]

@[expose] def b2Word : List Nat :=
  [
    2, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 1,
    0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0,
    1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 0, 2, 0
  ]

@[expose] def lb1Tab : Tab := wordTab letterTabs b1Word

@[expose] def lb2Tab : Tab := wordTab letterTabs b2Word

@[expose] def basisTabs (i : Fin 4) : Tab := fTab i.val

@[expose] def liftCheck : Bool :=
  decide (isInv lb1Tab = true ∧ isInv lb2Tab = true ∧ comm lb1Tab lb2Tab = true ∧
    normOK (elemTabs 1) lb1Tab = true ∧ normOK (elemTabs 1) lb2Tab = true) &&
  decide ((∀ c c' : Fin 4 → ZMod 2, monoTab basisTabs c = monoTab basisTabs c' → c = c') ∧
    (∀ y ∈ idTab :: elemTabs 1, ∃ c : Fin 4 → ZMod 2, monoTab basisTabs c = y)) &&
  decide (∀ i : Fin 4, tmul (tmul lb1Tab (basisTabs i)) lb1Tab = monoTab basisTabs (liftA1 i) ∧
    tmul (tmul lb2Tab (basisTabs i)) lb2Tab = monoTab basisTabs (liftA2 i))

end CFSG.EvenSporadicStandard.M23Std.LiftCheck
