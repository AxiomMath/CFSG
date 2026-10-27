module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerF4Data
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeF4

public section

namespace CFSG.AGLEmbedding

theorem f4InnerCheck_data : f4InnerCheck f4InnerData = true := by
  decide +kernel

theorem liftableNormalizerGen_F4Two (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.F4 q).Valid) (hp : q.p = 2) (he : q.exponent = 1) :
    LiftableNormalizerGen (TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.F4 q, hv⟩) := by
  have hK : Nat.card (ZMod 2) = q.card := by
    rw [Nat.card_zmod, TauCeti.PrimePower.card_def, hp, he, pow_one]
  obtain ⟨e⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_F4 q hv hp (ZMod 2) hK
  have hG := liftableNormalizerGen_of_f4InnerCheck (K := ZMod 2) (by simp) f4InnerData
    f4InnerCheck_data
  exact (hG.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot).symm).of_mulEquiv e

end CFSG.AGLEmbedding
