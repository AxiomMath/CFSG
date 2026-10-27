module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.LiftCheck

public section

namespace CFSG.EvenSporadicStandard.M22Std.HexadCheck

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.FusionCheck
  CFSG.EvenSporadicStandard.M22Std.LiftCheck

@[expose] def hexad : List Nat := [1, 2, 6, 11, 13, 16]

@[expose] def g5Word : List Nat := [0, 2, 0, 2, 0, 2, 0, 1, 0]

@[expose] def g3Word : List Nat := [0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0]

@[expose] def g5Tab : Tab := wordTab letterTabs g5Word

@[expose] def g3Tab : Tab := wordTab letterTabs g3Word

theorem hexad_fix : ∀ x < 22, (x ∈ hexad ↔ ∀ t ∈ elemTabs 1, t.getD x 0 = x) := by
  decide

set_option maxRecDepth 100000 in
theorem g5_norm : normOK (elemTabs 1) g5Tab = true := by decide

set_option maxRecDepth 100000 in
theorem g3_norm : normOK (elemTabs 1) g3Tab = true := by decide

set_option maxRecDepth 100000 in
theorem g5_pow : powTab g5Tab 5 = idTab := by decide

theorem g5_fix : g5Tab.getD 13 0 = 13 := by decide

set_option maxRecDepth 100000 in
theorem g5_moves : ∀ i : Fin 6, i ≠ 4 →
    g5Tab.getD (hexad.getD i.val 0) 0 ≠ hexad.getD i.val 0 := by
  decide

set_option maxRecDepth 100000 in
theorem g3_moves_p : g3Tab.getD 13 0 ≠ 13 := by decide

set_option maxRecDepth 100000 in
theorem g3_moves : (Finset.univ.filter
    fun i : Fin 6 => g3Tab.getD (hexad.getD i.val 0) 0 ≠ hexad.getD i.val 0).card = 3 := by
  decide

end CFSG.EvenSporadicStandard.M22Std.HexadCheck
