module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightSwapGen
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusFourMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapBounds

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus)
open CFSG.SeitzReduction.SeitzQ2 (SwapPairExclusion)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem false_of_swapRow_omega_minus_four (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K (by norm_num) b c))
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hrow : ∀ k : Fin (4 - 1),
      OmegaRowAt t (modelToG e (minusPairTorus (K := K) (by norm_num) b c k))
        (modelToG e (minusPairPerp (K := K) (by norm_num) b c k)) .swap)
    (hP : SwapPairExclusion
      (matrixProjectiveDerived (coordinateQuadMinus 4 K (by norm_num) b c))) : False := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  exact false_of_swapRow_omega_minus_four_of_gen hset hKc hq hirr e ht hKt hrow
    (minusFourSwapGenInput_holds hq hirr) hP

end Main

@[expose] def OmegaMinusFourLinearInvolutionInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (f : ℕ) (b c : K),
    (∀ s : K, s ^ 2 + b * s + c ≠ 0) → Nat.card K = 2 ^ f → 2 ≤ f →
      OmegaLinearInvolutionTwoPart (coordinateQuadMinus 4 K (by norm_num) b c) 4 f

theorem omegaMinusFourSwapRowInput_of_linear (hI : OmegaMinusFourLinearInvolutionInput) :
    OmegaMinusFourSwapRowInput := by
  intro G _ _ L hset f K _ _ _ b c hirr hKc hf2 e t ht hKt hrow
  have hq : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf2
  exact false_of_swapRow_omega_minus_four hset hKc hq hirr e ht hKt hrow
    (swapPairExclusion_coordinateMinus_of_linear hf2 hKc le_rfl _ hirr (hI K f b c hirr hKc hf2))

end CFSG.SeitzReduction.OmegaPilot
