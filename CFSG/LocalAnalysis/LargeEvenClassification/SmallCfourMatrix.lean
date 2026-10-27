module

public import CFSG.LocalAnalysis.LargeEvenClassification.RankTwoBinaryEndResidue

public section

namespace CFSG.LargeEvenClassification.Helpers

@[expose] def smallCfourUpper : RankTwoBinaryResidue 1 := ((0, 1), (0, 0))

@[expose] def smallCfourLower : RankTwoBinaryResidue 1 := ((0, 0), (1, 0))

@[expose] def smallCfourAllOnes : RankTwoBinaryResidue 1 := ((1, 1), (1, 1))

@[expose] def smallCfourRotation : RankTwoBinaryResidue 1 := ((0, 1), (1, 1))

private theorem smallCfour_norm_candidates :
    ∀ x : RankTwoBinaryResidue 1,
      (x = smallCfourUpper ∨ x = smallCfourLower ∨ x = smallCfourAllOnes ∨
        x = smallCfourRotation ∨ x = smallCfourRotation + 1) →
      x ≠ 0 ∧ ∃ y : RankTwoBinaryResidue 1, (1 + x) * y = 1 ∧ y * (1 + x) = 1 := by
  decide +kernel

private theorem smallCfour_candidate_sums :
    smallCfourUpper + smallCfourLower + smallCfourAllOnes = 1 ∧
      smallCfourRotation + (smallCfourRotation + 1) = 1 := by
  decide +kernel

theorem small_cfour_matrix_hyperplane_norm_element
    (W : Submodule (ZMod 2) (RankTwoBinaryResidue 1))
    (hdimension : Module.finrank (ZMod 2) W = 3) :
    ∃ f ∈ W, f ≠ 0 ∧ IsUnit (1 + f) := by
  have hproper : W < ⊤ := by
    refine lt_top_iff_ne_top.mpr ?_
    intro htop
    rw [htop, finrank_top, rankTwoBinaryResidue_finrank] at hdimension
    omega
  obtain ⟨functional, hnonzero, hle⟩ := Submodule.exists_le_ker_of_lt_top W hproper
  have hkerProper : functional.ker < ⊤ :=
    lt_top_iff_ne_top.mpr (mt LinearMap.ker_eq_top.mp hnonzero)
  have hkerSmall := Submodule.finrank_lt_finrank_of_lt hkerProper
  rw [finrank_top, rankTwoBinaryResidue_finrank] at hkerSmall
  have hkerLarge := Submodule.finrank_mono hle
  have hkernel : W = functional.ker :=
    Submodule.eq_of_le_of_finrank_eq hle (by omega)
  by_contra hnone
  have hone (x : RankTwoBinaryResidue 1)
      (hx : x = smallCfourUpper ∨ x = smallCfourLower ∨ x = smallCfourAllOnes ∨
        x = smallCfourRotation ∨ x = smallCfourRotation + 1) : functional x = 1 := by
    have hgood := smallCfour_norm_candidates x hx
    have hnotMem : x ∉ W := by
      intro hmem
      exact hnone ⟨x, hmem, hgood.1, isUnit_iff_exists.mpr hgood.2⟩
    have hnonzeroValue : functional x ≠ 0 := by
      intro hz
      apply hnotMem
      rw [hkernel]
      exact hz
    have hbinary : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
    exact hbinary _ hnonzeroValue
  have hn1 := hone smallCfourUpper (Or.inl rfl)
  have hn2 := hone smallCfourLower (Or.inr (Or.inl rfl))
  have hn3 := hone smallCfourAllOnes (Or.inr (Or.inr (Or.inl rfl)))
  have hr := hone smallCfourRotation (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hr1 := hone (smallCfourRotation + 1) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have hnSum := congrArg functional smallCfour_candidate_sums.1
  have hrSum := congrArg functional smallCfour_candidate_sums.2
  rw [map_add, map_add, hn1, hn2, hn3] at hnSum
  rw [map_add, hr, hr1] at hrSum
  have hbad : (1 : ZMod 2) + 1 + 1 = 1 + 1 := hnSum.trans hrSum.symm
  revert hbad
  decide

end CFSG.LargeEvenClassification.Helpers
