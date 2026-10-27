module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.LiftCheck

public section

namespace CFSG.EvenSporadicStandard.M23Std.HeptadCheck

open CFSG.EvenSporadicStandard.Wong77.M23Sylow CFSG.EvenSporadicStandard.M23Std.FusionCheck
  CFSG.EvenSporadicStandard.M23Std.LiftCheck

@[expose] def heptad : List Nat := [2, 4, 6, 15, 16, 19, 22]

@[expose] def g7Word : List Nat :=
  [
    2, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0,
    1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1,
    0, 1, 0, 0, 1, 0, 1, 0, 1
  ]

@[expose] def g3Word : List Nat :=
  [
    0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 1, 0,
    1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2,
    0, 1, 0, 1, 0, 0, 1, 0, 1
  ]

@[expose] def g7Tab : Tab := wordTab letterTabs g7Word

@[expose] def g3Tab : Tab := wordTab letterTabs g3Word

theorem heptad_fix : ∀ x < 23, (x ∈ heptad ↔ ∀ t ∈ elemTabs 1, t.getD x 0 = x) := by
  decide

set_option maxRecDepth 100000 in
theorem g7_norm : normOK (elemTabs 1) g7Tab = true := by decide

set_option maxRecDepth 100000 in
theorem g3_norm : normOK (elemTabs 1) g3Tab = true := by decide

set_option maxRecDepth 100000 in
theorem g7_pow : powTab g7Tab 7 = idTab := by decide

set_option maxRecDepth 100000 in
theorem g7_moves : ∀ i : Fin 7, g7Tab.getD (heptad.getD i.val 0) 0 ≠ heptad.getD i.val 0 := by
  decide

set_option maxRecDepth 100000 in
theorem g3_moves : (Finset.univ.filter
    fun i : Fin 7 => g3Tab.getD (heptad.getD i.val 0) 0 ≠ heptad.getD i.val 0).card = 3 := by
  decide

end CFSG.EvenSporadicStandard.M23Std.HeptadCheck
