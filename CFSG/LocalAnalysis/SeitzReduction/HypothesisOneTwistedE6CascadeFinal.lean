module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6Cascade
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6Kill

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K]


theorem twistedE6FrameReduction {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) : TwistedE6FrameReduction K σ.toRingHom :=
  twistedE6FrameReduction_of_kill hf hK hσ (twistedE6Kill hf hK hσ)


theorem exceptionalHypothesisOne : ExceptionalHypothesisOne :=
  exceptionalHypothesisOne_of_twistedE6Kill fun _ _ _ _ hf hK hσ => twistedE6Kill hf hK hσ

end CFSG.SeitzReduction
