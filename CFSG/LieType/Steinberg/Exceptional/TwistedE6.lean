module

public import CFSG.LieType.Steinberg.Conclusion
public import CFSG.LieType.Steinberg.TwistedE6.Datum
public import CFSG.LieType.Steinberg.TwistedE6.Generation
public import CFSG.LieType.Steinberg.Exceptional.Fields

public section

namespace CFSG.LieType.Steinberg

open CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional

universe w

theorem twistedDatum_conclusionA {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    ConclusionA.{0, w} (twistedDatum k θ) :=
  conclusionA_of (twistedDatum_isCTGroupDatum θ hθ (iSup_twistedDatum_rootGroup θ hθ))
    (twistedDatum_steinbergExtras θ hθ)

theorem twistedE6_conclusionA (p f : ℕ) [Fact p.Prime] (hf : 1 ≤ f) :
    ConclusionA.{0, w} (twistedE6Datum p f) :=
  twistedDatum_conclusionA (frobQ p f) (frobQ_frobQ p f hf)

end CFSG.LieType.Steinberg
