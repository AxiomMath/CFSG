module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanAlphaThreeLie
import CFSG.HardMathSupport.Lang.AlphaThree.TwistedATwo
import CFSG.HardMathSupport.Lang.AlphaThree.E6
import CFSG.HardMathSupport.Lang.AlphaThree.TwistedE6Final

public section

namespace CFSG.AGLEmbedding

open TauCeti

theorem primePower_eq_two_of_card {q : PrimePower} (hq : q.card = 2) :
    q.p = 2 ∧ q.exponent = 1 := by
  rw [PrimePower.card_def] at hq
  exact (Nat.prime_two.pow_eq_iff).mp hq


theorem alphaThreeLieResidual_holds : AlphaThreeLieResidual := by
  refine alphaThreeLieResidual_of_normalizerGen fun ⟨d, hv⟩ hd => ?_
  rcases hd with ⟨r, q, rfl, hr, -, hq⟩ | ⟨q, rfl, hq⟩ | ⟨q, rfl, hq⟩
  · obtain ⟨hp, he⟩ := primePower_eq_two_of_card hq
    exact CFSG.HardMathSupport.Lang.AlphaThree.liftableNormalizerGen_twistedA_two r q hv hr hp he
  · exact CFSG.HardMathSupport.Lang.AlphaThree.liftableNormalizerGen_E6 q hv hq
  · exact CFSG.HardMathSupport.Lang.AlphaThree.liftableNormalizerGen_twistedE6 q hv hq

end CFSG.AGLEmbedding
