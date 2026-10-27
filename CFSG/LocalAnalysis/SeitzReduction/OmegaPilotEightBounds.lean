module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightBoundsLagrangian
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightSwapMinusMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightBoundsSmall

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.OrthogonalInvolutions (commSpace two_mul_finrank_commSpace_le)
open CFSG.SeitzReduction.SeitzQ2 (SwapPairExclusion)

section Bound

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_twoSubgroup_centralizer_four
    {Q : QuadraticForm K (Fin (2 * 4) → K)} (hQ : (polarBilin Q).Nondegenerate)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    {s : GL (Fin (2 * 4)) K} (hs : s ∈ matrixIsometries Q) (hss : s * s = 1) :
    ∃ R : Subgroup (GL (Fin (2 * 4)) K), IsPGroup 2 R ∧
      R ≤ matrixDerived Q ⊓ Subgroup.centralizer {s} ∧ Nat.card K ^ 8 ≤ Nat.card R := by
  have htt : matrixLinearIso s * matrixLinearIso s = 1 := by rw [← map_mul, hss, map_one]
  have hle := two_mul_finrank_commSpace_le (K := K) htt
  rw [Module.finrank_fin_fun] at hle
  rcases Nat.lt_or_ge (Module.finrank K (commSpace (matrixLinearIso s))) 4 with hlt | hge
  · exact exists_twoSubgroup_centralizer_of_finrank_lt_four hQ hE hs hss hlt
  · exact exists_twoSubgroup_centralizer_of_lagrangian_of_four_le le_rfl hQ hE hs hss
      (by omega)

theorem omegaLinearInvolutionMatrixTwoPart_four {f : ℕ} (hK : Nat.card K = 2 ^ f)
    {Q : QuadraticForm K (Fin (2 * 4) → K)} (hQ : (polarBilin Q).Nondegenerate)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) : OmegaLinearInvolutionMatrixTwoPart Q 4 f := by
  intro s hs hss _
  obtain ⟨R, hR2, hRle, hRcard⟩ := exists_twoSubgroup_centralizer_four hQ hE hs hss
  refine ⟨R, hR2, hRle, ?_⟩
  have h2 := Nat.pow_le_pow_left hRcard 2
  rw [hK, ← pow_mul, ← pow_mul] at h2
  refine le_trans (le_of_eq ?_) h2
  congr 1

theorem omegaLinearInvolutionTwoPart_four {f : ℕ} (hK : Nat.card K = 2 ^ f)
    {Q : QuadraticForm K (Fin (2 * 4) → K)} (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * 4) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) : OmegaLinearInvolutionTwoPart Q 4 f := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have := Finite.one_lt_card (α := K)
      rw [hK, pow_zero] at this
      omega
    · exact h
  have hZ := (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.evenOrthogonalRealization_of_regular
    hf hK (by omega) Q hQ hT hE).1
  exact omegaLinearInvolutionTwoPart_of_matrix hZ (omegaLinearInvolutionMatrixTwoPart_four hK hQ hE)

theorem omegaLinearInvolutionTwoPart_coordinatePlus_four {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    OmegaLinearInvolutionTwoPart (coordinateQuadPlus 4 K) 4 f :=
  omegaLinearInvolutionTwoPart_four hK (regular_coordinateQuadPlus 4 K (by norm_num)).1
    (regular_coordinateQuadPlus 4 K (by norm_num)).2
    (commutator_coordinateQuadPlus 4 K (by norm_num))

theorem omegaLinearInvolutionTwoPart_coordinateMinus_four {f : ℕ} (hK : Nat.card K = 2 ^ f)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    OmegaLinearInvolutionTwoPart (coordinateQuadMinus 4 K (by norm_num) b c) 4 f :=
  omegaLinearInvolutionTwoPart_four hK (regular_coordinateQuadMinus 4 K b c le_rfl hirr).1
    (regular_coordinateQuadMinus 4 K b c le_rfl hirr).2
    (commutator_coordinateQuadMinus 4 K b c le_rfl hirr)

end Bound

section Minus

theorem omegaMinusFourLinearInvolutionInput_holds : OmegaMinusFourLinearInvolutionInput :=
  fun _ _ _ _ _ _ _ hirr hK _ => omegaLinearInvolutionTwoPart_coordinateMinus_four hK hirr

theorem omegaMinusFourSwapRowInput_holds : OmegaMinusFourSwapRowInput :=
  omegaMinusFourSwapRowInput_of_linear omegaMinusFourLinearInvolutionInput_holds

end Minus

end CFSG.SeitzReduction.OmegaPilot
