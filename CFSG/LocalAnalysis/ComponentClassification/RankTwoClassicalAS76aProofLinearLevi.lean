module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard

theorem exists_unit_ne_one {K : Type} [Field K] (h4 : ∃ s : Finset K, s.card = 4) :
    ∃ c : Kˣ, c ≠ 1 := by
  classical
  obtain ⟨s, hs⟩ := h4
  obtain ⟨ω, -, hω0, hω1⟩ : ∃ ω ∈ s, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : s ⊆ {0, 1} := fun x hx => by
      by_cases h0 : x = 0
      · simp [h0]
      · simp [hcon x hx h0]
    have := (Finset.card_le_card hsub).trans Finset.card_le_two
    omega
  refine ⟨Units.mk0 ω hω0, fun h => hω1 ?_⟩
  have := congrArg Units.val h
  rwa [Units.val_mk0, Units.val_one] at this

theorem barW_le_centralizer_barL {K : Type} [Field K] {k : ℕ} :
    barW K k ≤ centralizer (barL K k : Set (projectiveSL (2 + k) K)) := fun _ hw =>
  mem_centralizer_iff.mpr fun _ hl => (barW_commute_barL hw hl).symm

theorem barT_le_centralizer_barL {K : Type} [Field K] :
    barT K ≤ centralizer (barL K 2 : Set (projectiveSL (2 + 2) K)) := by
  rintro _ ⟨c, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨S, rfl⟩
  simp only [MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_blkSL₂]
  exact blk_mul_torus _ _ c

end CFSG.ComponentClassification.RankTwoClassical
