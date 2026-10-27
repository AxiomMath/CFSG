module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerE6Data
import CFSG.Adapters.TauCetiExceptional.EvenBridgeE6E7

public section

namespace CFSG.AGLEmbedding

theorem e6InnerCheck_data : e6InnerCheck e6InnerData = true := by
  decide +kernel

theorem liftableNormalizerGen_E6Two (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E6 q).Valid) (hp : q.p = 2) (he : q.exponent = 1) :
    LiftableNormalizerGen (TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.E6 q, hv⟩) := by
  have hK : Nat.card (ZMod 2) = q.card := by
    rw [Nat.card_zmod, TauCeti.PrimePower.card_def, hp, he, pow_one]
  obtain ⟨e⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_E6 q hv hp (ZMod 2) hK
  have hG := liftableNormalizerGen_of_e6InnerCheck (K := ZMod 2) (by simp) e6InnerData
    e6InnerCheck_data
  exact (hG.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot).symm).of_mulEquiv e

end CFSG.AGLEmbedding
