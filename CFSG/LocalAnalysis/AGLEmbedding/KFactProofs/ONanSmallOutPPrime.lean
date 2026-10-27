module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallOutSpor
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneKFacts

public section

namespace CFSG.AGLEmbedding

open KFactProofs.SmallIdent

theorem kFactSmallOutPPrime_of_smallIdent
    (h : KFactSmallIdent) : KFactSmallOutPPrime := by
  intro K _ _ hs hnab hc p hp hp2 T hT hΓ hAut hL34 f hf
  have hK := isSmallStrongP_of_autRank h hs hnab hc hp hp2 T hT hΓ hAut
  rcases hK with hL | hU | hA | ⟨h3, hL34' | hM⟩ | ⟨h5, hTits | hMcL | hFi⟩ | ⟨h11, hJ⟩
  · exact autPInner_of_isSmallLinTwo hp hp2 hL f hf
  · exact autPInner_of_isSmallUnitary hp hp2 hs hnab hU f hf
  · exact autPInner_of_isAltTwoP hp hp2 hA f hf
  · exact absurd ⟨h3, hL34'⟩ hL34
  · exact autPInner_of_isM11 hM f hf
  · exact autPInner_of_isTitsGroup hp hp2 hTits f hf
  · exact autPInner_of_isMcL hp hp2 hs hMcL f hf
  · exact autPInner_of_isFi22 hp hp2 hs hFi f hf
  · exact autPInner_of_isJ4 hp hp2 hs hJ f hf

end CFSG.AGLEmbedding
