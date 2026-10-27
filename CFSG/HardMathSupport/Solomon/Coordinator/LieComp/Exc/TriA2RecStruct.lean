module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2Rec

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open scoped MatrixGroups

set_option linter.unusedSectionVars false

theorem sl3_hom_structure {F : Type} [Field F] [Finite F] {C : Type} [Group C] [Finite C]
    (ρ : SL(3, F) →* C) (hρ : ∃ g, ρ g ≠ 1) (hcard : Nat.card C = Nat.card SL(3, F)) :
    ρ.ker ≤ Subgroup.center SL(3, F) ∧
      ∃ _ : ρ.range.Normal, Group.IsSolvable (C ⧸ ρ.range) := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hquasi' : CFSG.IsQuasisimple SL(3, F) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 3 F
      (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))
  have hquasi : CFSG.Open.IsQuasisimple SL(3, F) :=
    CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mp hquasi'
  have hker : ρ.ker ≤ Subgroup.center SL(3, F) := by
    obtain ⟨g, hg⟩ := hρ
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hquasi ρ.ker with
      h | h
    · exact h
    · exact absurd (h ▸ Subgroup.mem_top g : g ∈ ρ.ker) hg
  have hkercard : Nat.card ρ.ker ≤ 3 :=
    (Subgroup.card_le_of_le hker).trans CFSG.DesarguesianPlanes.card_center_SL3_le
  have hrange : Nat.card ρ.range * Nat.card ρ.ker = Nat.card (SL(3, F)) := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv,
      ← Subgroup.index_eq_card, Subgroup.index_mul_card]
  have hidx : ρ.range.index * Nat.card ρ.range = Nat.card C := ρ.range.index_mul_card
  have hpos : 0 < Nat.card ρ.range := Nat.card_pos
  have h1 : ρ.range.index * Nat.card ρ.range ≤ 3 * Nat.card ρ.range := by
    rw [hidx, hcard, ← hrange]
    nlinarith
  have hidx3 : ρ.range.index ≤ 3 := Nat.le_of_mul_le_mul_right h1 hpos
  have hidx0 : ρ.range.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  haveI : Group.IsPerfect SL(3, F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  haveI : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  exact ⟨hker, normal_and_solvable_of_perfect_index_le_four inferInstance (by omega) hidx0⟩

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
