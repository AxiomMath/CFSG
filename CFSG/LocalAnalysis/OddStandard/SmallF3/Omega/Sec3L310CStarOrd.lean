module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Lemma32
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Syl
public import CFSG.Blueprint.SourceClassicalTransport

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem isQuasisimple_of_isFStarGroup {L : Type} [Group L] (h : IsFStarGroup L) :
    IsQuasisimple L :=
  h.elim (fun h => h.1) (fun h => h.1)

theorem card_of_pOmegaPlus {Q : Type} [Group Q] (h : LieModel Q .POmegaPlus 4 3 1) :
    Nat.card Q = 4952179814400 := by
  rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Q)
    (show (3 : ℕ) ≠ 2 by norm_num) (h.statedClassicalModel_of_ne_zero (by norm_num))).2.2.2.2.1
    rfl]
  decide +kernel

theorem nonempty_equiv_of_pOmegaPlus {Q Q' : Type} [Group Q] [Group Q']
    (h : LieModel Q .POmegaPlus 4 3 1) (h' : LieModel Q' .POmegaPlus 4 3 1) :
    Nonempty (Q ≃* Q') :=
  CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel
    (h.statedClassicalModel_of_ne_zero (by norm_num))
    (h'.statedClassicalModel_of_ne_zero (by norm_num))

theorem lieModel_or_not_dvd_of_isFStarGroup {L : Type} [Group L] [Finite L]
    (hS : IsFStarGroup L) :
    LieModel (L ⧸ oddCore L) .POmegaPlus 4 3 1 ∨
      (1 < Nat.card (L ⧸ oddCore L) ∧ ¬ 4952179814400 ∣ Nat.card (L ⧸ oddCore L)) := by
  by_cases hF : IsFGroup L
  · obtain ⟨-, hQ⟩ := hF
    rcases hQ with h | h
    · rcases h with h | h | h | h | h | h
      · right
        have hcard : Nat.card (L ⧸ oddCore L) = 25920 := by
          rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := L ⧸ oddCore L)
            (show (3 : ℕ) ≠ 2 by norm_num)
            (h.statedClassicalModel_of_ne_zero (by norm_num))).2.2.1 rfl]
          decide +kernel
        rw [hcard]
        exact ⟨by norm_num, by decide +kernel⟩
      · right
        have hcard : Nat.card (L ⧸ oddCore L) = 6065280 := by
          rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := L ⧸ oddCore L)
            (show (3 : ℕ) ≠ 2 by norm_num)
            (h.statedClassicalModel_of_ne_zero (by norm_num))).1 rfl]
          decide +kernel
        rw [hcard]
        exact ⟨by norm_num, by decide +kernel⟩
      · right
        have hcard : Nat.card (L ⧸ oddCore L) = 3265920 := by
          rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := L ⧸ oddCore L)
            (show (3 : ℕ) ≠ 2 by norm_num)
            (h.statedClassicalModel_of_ne_zero (by norm_num))).2.1 rfl]
          decide +kernel
        rw [hcard]
        exact ⟨by norm_num, by decide +kernel⟩
      · right
        have hcard : Nat.card (L ⧸ oddCore L) = 4585351680 := by
          rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := L ⧸ oddCore L)
            (show (3 : ℕ) ≠ 2 by norm_num)
            (h.statedClassicalModel_of_ne_zero (by norm_num))).2.2.2.1 rfl]
          decide +kernel
        rw [hcard]
        exact ⟨by norm_num, by decide +kernel⟩
      · exact Or.inl h
      · right
        have hcard : Nat.card (L ⧸ oddCore L) = 10151968619520 := by
          rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := L ⧸ oddCore L)
            (show (3 : ℕ) ≠ 2 by norm_num)
            (h.statedClassicalModel_of_ne_zero (by norm_num))).2.2.2.2.2 rfl]
          decide +kernel
        rw [hcard]
        exact ⟨by norm_num, by decide +kernel⟩
    · right
      rw [card_of_isTwoU43 h]
      exact ⟨by norm_num, by decide +kernel⟩
  · right
    rcases card_quotient_oddCore_of_isFStarGroup_not_isFGroup hS hF with h | h | h | h <;>
      rw [h] <;> exact ⟨by norm_num, by decide +kernel⟩

theorem lieModel_of_dvd_card {L : Type} [Group L] [Finite L] (hS : IsFStarGroup L)
    (hd : 4952179814400 ∣ Nat.card (L ⧸ oddCore L)) :
    LieModel (L ⧸ oddCore L) .POmegaPlus 4 3 1 :=
  (lieModel_or_not_dvd_of_isFStarGroup hS).resolve_right fun h => h.2 hd

theorem one_lt_card_quotient_oddCore {L : Type} [Group L] [Finite L] (hS : IsFStarGroup L) :
    1 < Nat.card (L ⧸ oddCore L) := by
  rcases lieModel_or_not_dvd_of_isFStarGroup hS with h | h
  · rw [card_of_pOmegaPlus h]
    norm_num
  · exact h.1

theorem oddCore_le_center_of_isFStarGroup {L : Type} [Group L] [Finite L] (hS : IsFStarGroup L) :
    oddCore L ≤ center L := by
  have hq : IsQuasisimple L := isQuasisimple_of_isFStarGroup hS
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (inferInstance : (oddCore L).Normal) with
    h | h
  · exfalso
    have h1 : Nat.card (L ⧸ oddCore L) = 1 := by
      rw [h, ← Subgroup.index_eq_card]
      exact Subgroup.index_top
    have := one_lt_card_quotient_oddCore hS
    omega
  · exact h

theorem card_quotient_center_dvd_card_quotient_oddCore {L : Type} [Group L] [Finite L]
    (hS : IsFStarGroup L) : Nat.card (L ⧸ center L) ∣ Nat.card (L ⧸ oddCore L) := by
  rw [← Subgroup.index_eq_card, ← Subgroup.index_eq_card]
  exact Subgroup.index_dvd_of_le (oddCore_le_center_of_isFStarGroup hS)

theorem center_eq_oddCore_of_pOmegaPlus [Finite G] {Y : Subgroup G} (hY : InFStar Y)
    (h : LieModel (↥Y ⧸ oddCore ↥Y) .POmegaPlus 4 3 1) : center ↥Y = oddCore ↥Y :=
  le_antisymm (center_le_oddCore_of_pOmegaPlus h) (oddCore_le_center_of_isFStarGroup hY)

theorem nonempty_equiv_center_quotient_of_pOmegaPlus [Finite G] {Y Y' : Subgroup G}
    (hY : InFStar Y) (hY' : InFStar Y') (h : LieModel (↥Y ⧸ oddCore ↥Y) .POmegaPlus 4 3 1)
    (h' : LieModel (↥Y' ⧸ oddCore ↥Y') .POmegaPlus 4 3 1) :
    Nonempty (↥Y ⧸ center ↥Y ≃* ↥Y' ⧸ center ↥Y') := by
  obtain ⟨e⟩ := nonempty_equiv_of_pOmegaPlus h h'
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (center_eq_oddCore_of_pOmegaPlus hY h)).trans
    (e.trans (QuotientGroup.quotientMulEquivOfEq
      (center_eq_oddCore_of_pOmegaPlus hY' h')).symm)⟩

end CFSG.OddStandard.SmallF3.Omega
