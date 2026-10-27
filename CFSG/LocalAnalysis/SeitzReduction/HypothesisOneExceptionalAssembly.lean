module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneE6OuterSquare
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4ClassDescent
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassListE6
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassListE7
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassListE8

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem innerInvolutionInput_untwisted_exceptional (τ : Tag) (f : ℕ) (K : Type) [Field K] (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    InnerInvolutionInput (adjointGroup τ K) := by
  rcases hτ with rfl | rfl | rfl | rfl
  · exact innerInvolutionInput_F4' hf hK
  · exact innerInvolutionInput_E6' hf hK
  · exact innerInvolutionInput_E7' hf hK
  · exact innerInvolutionInput_E8' hf hK


theorem exceptionalHypothesisOne_of_twistedE6
    (hinT : ∀ (f : ℕ) (K : Type) [Field K] (σ : K ≃+* K), 1 ≤ f → Nat.card K = (2 ^ f) ^ 2 →
      (∀ c, σ c = c ^ 2 ^ f) → InnerInvolutionInput (graphFixedRootGroup .E6 K σ.toRingHom)) :
    ExceptionalHypothesisOne :=
  exceptionalHypothesisOne_of_inner' (fun τ f K _ hf hK hτ =>
    innerInvolutionInput_untwisted_exceptional τ f K hf hK hτ) hinT

end CFSG.SeitzReduction
