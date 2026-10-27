module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFShapes

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem ff_card_model_psu3 {X : Type} [Group X] (h : LieModel X .PSU 3 3 1) :
    Nat.card X = 6048 :=
  LieModel.card_psu_three_three h

theorem ff_fin_simple_psu3 {X : Type} [Group X] (h : LieModel X .PSU 3 3 1) :
    Finite X ∧ IsSimpleGroup X := by
  have := CFSG.LieType.Simplicity.fam_classical_converse X
    ⟨.PSU, 3, 3, 1, h.statedClassicalModel_of_ne_zero (by norm_num : (3 : ℕ) ≠ 0)⟩
  exact ⟨this.1, this.2.2⟩

theorem ff_simple_of_lieModel_psu3 {X : Type} [Group X] (h : LieModel X .PSU 3 3 1) :
    IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨hfin, hs⟩ := ff_fin_simple_psu3 h
  haveI := hfin
  exact ⟨hs, ff_noncomm_of_simple_card hs (by rw [ff_card_model_psu3 h]; norm_num)⟩

theorem ff_isU33_of_lieModel {X : Subgroup G} (h : LieModel ↥X .PSU 3 3 1) : IsU33 X := by
  obtain ⟨hfin, hs⟩ := ff_fin_simple_psu3 h
  haveI := hfin
  exact ff_lieModel_quot_oddCore h hs (by rw [ff_card_model_psu3 h]; norm_num)

theorem ff_card_isU33 {X : Subgroup G} (h : IsU33 X) : Nat.card (↥X ⧸ oddCore ↥X) = 6048 :=
  ff_card_model_psu3 h

theorem ff_isU33_ne_bot {X : Subgroup G} (h : IsU33 X) : X ≠ ⊥ := by
  intro hX
  have h1 := ff_card_quot_bot hX
  have h2 := ff_card_isU33 h
  omega

theorem ff_not_isU33_and_isL29 {X : Subgroup G} (h : IsU33 X) : ¬ IsL29 X := by
  intro h'
  have h1 := ff_card_isU33 h
  have h2 := ff_card_isL29 h'
  omega

theorem ff_not_isU33_and_isOmega5 {X : Subgroup G} (h : IsU33 X) : ¬ IsOmega5 X := by
  intro h'
  have h1 := ff_card_isU33 h
  have h2 := ff_card_isOmega5 h'
  omega

end CFSG.OddStandard.SmallF3.Omega
