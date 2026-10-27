module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeChevTwo
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover

public section

namespace CFSG.AGLEmbedding

theorem kFactChevTwoInnerGen_of_normalizerGen
    (h : ∀ d : TauCeti.ValidLieTypeIndex, IsChevTwoInnerIndex d →
      LiftableNormalizerGen (TauCeti.CFSGIndex.lie d).Group) : KFactChevTwoInnerGen := by
  intro d hd K _ _ _ ⟨e⟩ hZ _ T
  exact weakCore_eq_top_of_normalizerGen (h d hd) e hZ T

end CFSG.AGLEmbedding
