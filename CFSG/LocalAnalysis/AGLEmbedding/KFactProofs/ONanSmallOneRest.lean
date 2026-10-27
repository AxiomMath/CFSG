module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltOne
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallM11Local
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallMcLLocal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallOutSpor
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallTitsLocal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactReduceRankOne

public section

namespace CFSG.AGLEmbedding

open KFactProofs.SmallIdent CFSG.AGLEmbeddingD2

theorem kFactOneSmallRest_of_smallIdent
    (hJ4 : D2HeisLocalAt (.sporadic .J4) fun p => p = 11) (h : KFactSmallIdent) :
    KFactOneSmallRest := by
  intro K _ _ hs hnab hc p hp hp2 T hT hΓ hAut hL34 hFi hLU
  rcases isSmallStrongP_of_autRank h hs hnab hc hp hp2 T hT hΓ hAut with
    hK | hK | hK | ⟨rfl, hK | hK⟩ | ⟨rfl, hK | hK | hK⟩ | ⟨rfl, hK⟩
  · exact absurd (Or.inl hK) hLU
  · exact absurd (Or.inr hK) hLU
  · exact oneSmallFacts_of_isAltTwoP hp hp2 hK T
  · exact absurd ⟨rfl, hK⟩ hL34
  · exact oneSmallFacts_of_sporCore hp (sporCore_m11 hK T) (autFixInner_m11 hK T)
      (autPInner_of_isM11 hK)
  · exact oneSmallFacts_of_sporCore hp (sporCore_of_isTitsGroup hs hnab hK T)
      (autFixInner_of_isTitsGroup hs hnab hK T) (autPInner_of_isTitsGroup hp hp2 hK)
  · exact oneSmallFacts_of_sporCore hp (sporCore_of_isMcL hs hnab hK T)
      (autFixInner_of_isMcL hs hnab hK T) (autPInner_of_isMcL hp hp2 hs hK)
  · exact absurd ⟨rfl, hK⟩ hFi
  · exact oneSmallFacts_of_sporCore hp (sporCore_of_d2HeisLocalAt hp (by norm_num) hJ4 hs hnab hK T)
      (autFixInner_of_d2HeisLocalAt hp hJ4 hs hnab hK T) (autPInner_of_isJ4 hp hp2 hs hK)

end CFSG.AGLEmbedding
