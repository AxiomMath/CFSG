module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.Defs
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (unitary_full_diagonal_outer_order)
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU unitaryPSUEquiv)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LieType.Multipliers.U43 (F9)

theorem unitaryFieldData_f9 : UnitaryFieldData 3 1 F9 :=
  ⟨Nat.prime_three, le_rfl, by rw [Nat.card_eq_fintype_card, F9.card_eq]; norm_num⟩

noncomputable def unitaryPSUEquivU43 : unitaryPSU unitaryFieldData_f9 4 ≃* U43 :=
  unitaryPSUEquiv unitaryFieldData_f9 (by norm_num)

theorem card_outer_u43 : Nat.card (Outer U43) = 8 := by
  obtain ⟨-, -, -, -, h, -⟩ := unitary_full_diagonal_outer_order unitaryFieldData_f9 (n := 4)
    (by norm_num) (by norm_num)
  rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
    unitaryPSUEquivU43).toEquiv, h]
  norm_num

theorem outU43TwoGroup : OutU43TwoGroup :=
  IsPGroup.of_card (n := 3) (by rw [card_outer_u43]; norm_num)

end CFSG.EvenSporadicStandard.RuStd.S2
