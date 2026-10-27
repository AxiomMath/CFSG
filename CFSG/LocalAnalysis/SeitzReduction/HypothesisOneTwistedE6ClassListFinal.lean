module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassList
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6Classes
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneExceptionalAssembly

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K]


theorem innerInvolutionInput_twistedE6_of_frameReduction {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (hred : TwistedE6FrameReduction K σ.toRingHom) :
    InnerInvolutionInput (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
  innerInvolutionInput_twistedE6_of_classes hf hK hσ (twistedE6_hrep_of_frameReduction hf hK hσ hred)


theorem exceptionalHypothesisOne_of_twistedE6FrameReduction
    (hred : ∀ (f : ℕ) (K : Type) [Field K] (σ : K ≃+* K), 1 ≤ f → Nat.card K = (2 ^ f) ^ 2 →
      (∀ c, σ c = c ^ 2 ^ f) → TwistedE6FrameReduction K σ.toRingHom) :
    ExceptionalHypothesisOne :=
  exceptionalHypothesisOne_of_twistedE6 fun f K _ σ hf hK hσ =>
    innerInvolutionInput_twistedE6_of_frameReduction hf hK hσ (hred f K σ hf hK hσ)

theorem exceptionalHypothesisOne_of_twistedE6CascadeReduction
    (hred : ∀ (f : ℕ) (K : Type) [Field K] (σ : K ≃+* K), 1 ≤ f → Nat.card K = (2 ^ f) ^ 2 →
      (∀ c, σ c = c ^ 2 ^ f) → TwistedE6CascadeReduction K σ.toRingHom) :
    ExceptionalHypothesisOne :=
  exceptionalHypothesisOne_of_twistedE6FrameReduction fun f K _ σ hf hK hσ =>
    (hred f K σ hf hK hσ).frameReduction

end CFSG.SeitzReduction
