module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBasic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltUPrime
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallM11Local
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallMcLLocal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallTitsLocal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactReduceRankOne

public section

namespace CFSG.AGLEmbedding

open KFactProofs.SmallIdent CFSG.AGLEmbeddingD2

theorem kFactUPrimeSmallRest_of_smallIdent
    (hJ4 : D2HeisLocalAt (.sporadic .J4) fun p => p = 11) (h : KFactSmallIdent) :
    KFactUPrimeSmallRest := by
  intro K _ _ hs hnab hc p hp hp2 T hT hΓ hAut hL34 hFi hLU
  rcases isSmallStrongP_of_autRank h hs hnab hc hp hp2 T hT hΓ hAut with
    hK | hK | hK | ⟨rfl, hK | hK⟩ | ⟨rfl, hK | hK | hK⟩ | ⟨rfl, hK⟩
  · exact absurd (Or.inl hK) hLU
  · exact absurd (Or.inr hK) hLU
  · exact kFactUPrime_of_isAltTwoP hp hp2 hK
  · exact absurd ⟨rfl, hK⟩ hL34
  · exact kFactUPrime_of_sporCore hp (sporCore_m11 hK) (autFixInner_m11 hK)
  · exact kFactUPrime_of_sporCore hp (sporCore_of_isTitsGroup hs hnab hK)
      (autFixInner_of_isTitsGroup hs hnab hK)
  · exact kFactUPrime_of_sporCore hp (sporCore_of_isMcL hs hnab hK)
      (autFixInner_of_isMcL hs hnab hK)
  · exact absurd ⟨rfl, hK⟩ hFi
  · exact kFactUPrime_of_sporCore hp (sporCore_of_d2HeisLocalAt hp (by norm_num) hJ4 hs hnab hK)
      (autFixInner_of_d2HeisLocalAt hp hJ4 hs hnab hK)

end CFSG.AGLEmbedding
