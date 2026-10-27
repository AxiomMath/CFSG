module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerKFact
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerSp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerUnitaryCarrier
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerOmegaCarrier
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerF4
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerE6

public section

namespace CFSG.AGLEmbedding

theorem kFactChevTwoInnerGen_of_certificates : KFactChevTwoInnerGen := by
  refine kFactChevTwoInnerGen_of_normalizerGen ?_
  rintro ⟨c, hv⟩ ⟨q, hq2, hq1, hc⟩
  rcases hc with hc | hc | hc | hc | hc | hc <;> simp only at hc <;> subst hc
  · exact liftableNormalizerGen_B4Two q hv hq2 hq1
  · exact liftableNormalizerGen_twistedA4Two q hv hq2 hq1
  · exact liftableNormalizerGen_twistedA5Two q hv hq2 hq1
  · exact liftableNormalizerGen_D4Two q hv hq2 hq1
  · exact liftableNormalizerGen_F4Two q hv hq2 hq1
  · exact liftableNormalizerGen_E6Two q hv hq2 hq1

end CFSG.AGLEmbedding
