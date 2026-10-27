module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapBoundsInvolution
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapBoundsLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapBoundsTwoGroup

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.OrthogonalInvolutions (commSpace two_mul_finrank_commSpace_le)
open CFSG.SeitzReduction.SeitzQ2 (SwapPairExclusion)

section Reduction

variable {K : Type} [Field K] {d : ℕ}

@[expose] def OmegaLagrangianInvolutionTwoPart (Q : QuadraticForm K (Fin d → K)) (n f : ℕ) :
    Prop :=
  ∀ s ∈ matrixIsometries Q, s * s = 1 →
    Module.finrank K (commSpace (matrixLinearIso s)) = n →
    ∃ R : Subgroup (GL (Fin d) K), IsPGroup 2 R ∧
      R ≤ matrixDerived Q ⊓ Subgroup.centralizer {s} ∧
      2 ^ (f * (n * (n - 1) + 4)) ≤ Nat.card R ^ 2

variable [Finite K] [CharP K 2]

theorem omegaLinearInvolutionMatrixTwoPart_of_lagrangian {n f : ℕ} (hn : 5 ≤ n)
    (hK : Nat.card K = 2 ^ f) {Q : QuadraticForm K (Fin (2 * n) → K)}
    (hQ : (polarBilin Q).Nondegenerate)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hL : OmegaLagrangianInvolutionTwoPart Q n f) : OmegaLinearInvolutionMatrixTwoPart Q n f := by
  intro s hs hss hs1
  have htt : matrixLinearIso s * matrixLinearIso s = 1 := by rw [← map_mul, hss, map_one]
  have hle := two_mul_finrank_commSpace_le (K := K) htt
  rw [Module.finrank_fin_fun] at hle
  rcases Nat.lt_or_ge (Module.finrank K (commSpace (matrixLinearIso s))) n with hlt | hge
  · obtain ⟨R, hR2, hRle, hRcard⟩ :=
      exists_twoSubgroup_centralizer_of_finrank_lt hn hQ hE hs hss hlt
    refine ⟨R, hR2, hRle, ?_⟩
    have e1 : 2 * (n * (n - 1) / 2) = n * (n - 1) :=
      Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd
    have h2 := Nat.pow_le_pow_left hRcard 2
    rw [hK, ← pow_mul, ← pow_mul] at h2
    refine le_trans (le_of_eq ?_) h2
    congr 1
    congr 1
    omega
  · exact hL s hs hss (by omega)

theorem omegaLinearInvolutionTwoPart_of_lagrangian {n f : ℕ} (hn : 5 ≤ n)
    (hK : Nat.card K = 2 ^ f) {Q : QuadraticForm K (Fin (2 * n) → K)}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hL : OmegaLagrangianInvolutionTwoPart Q n f) : OmegaLinearInvolutionTwoPart Q n f := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have := Finite.one_lt_card (α := K)
      rw [hK, pow_zero] at this
      omega
    · exact h
  have hZ := (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.evenOrthogonalRealization_of_regular
    hf hK (by omega) Q hQ hT hE).1
  exact omegaLinearInvolutionTwoPart_of_matrix hZ
    (omegaLinearInvolutionMatrixTwoPart_of_lagrangian hn hK hQ hE hL)

end Reduction

section Coordinate

variable {K : Type} [Field K] [Finite K] {f n : ℕ}

theorem swapPairExclusion_coordinatePlus_of_lagrangian (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 5 ≤ n) (hL : OmegaLagrangianInvolutionTwoPart (coordinateQuadPlus n K) n f) :
    SwapPairExclusion (matrixProjectiveDerived (coordinateQuadPlus n K)) := by
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hK
  have hreg := regular_coordinateQuadPlus n K (by omega)
  exact swapPairExclusion_coordinatePlus_of_linear hf hK hn
    (omegaLinearInvolutionTwoPart_of_lagrangian hn hK hreg.1 hreg.2
      (commutator_coordinateQuadPlus n K (by omega)) hL)

theorem swapPairExclusion_coordinateMinus_of_lagrangian (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 5 ≤ n) (h1 : 1 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hL : OmegaLagrangianInvolutionTwoPart (coordinateQuadMinus n K h1 b c) n f) :
    SwapPairExclusion (matrixProjectiveDerived (coordinateQuadMinus n K h1 b c)) := by
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hK
  have hreg := regular_coordinateQuadMinus n K b c (by omega) hirr
  exact swapPairExclusion_coordinateMinus_of_linear hf hK (by omega) h1 hirr
    (omegaLinearInvolutionTwoPart_of_lagrangian hn hK hreg.1 hreg.2
      (commutator_coordinateQuadMinus n K b c (by omega) hirr) hL)

theorem omegaPlusLinearInvolutionInput_of_lagrangian (hn : 5 ≤ n)
    (hL : ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (e : ℕ), Nat.card F = 2 ^ e →
      OmegaLagrangianInvolutionTwoPart (coordinateQuadPlus n F) n e) :
    OmegaPlusLinearInvolutionInput n :=
  omegaPlusLinearInvolutionInput_of_linear hn fun F _ _ _ e he => by
    have hreg := regular_coordinateQuadPlus n F (by omega)
    exact omegaLinearInvolutionTwoPart_of_lagrangian hn he hreg.1 hreg.2
      (commutator_coordinateQuadPlus n F (by omega)) (hL F e he)

end Coordinate

end CFSG.SeitzReduction.OmegaPilot
