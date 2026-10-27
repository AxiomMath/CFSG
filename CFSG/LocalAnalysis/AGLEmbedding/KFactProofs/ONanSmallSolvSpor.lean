module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBasic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallM11Local
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallMcLLocal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallTitsLocal
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormal

public section

namespace CFSG.AGLEmbedding

open KFactProofs.SmallIdent CFSG.AGLEmbeddingD2

theorem kFactSmallGammaSolvableSpor_of_smallIdent
    (hJ4 : D2HeisLocalAt (.sporadic .J4) fun p => p = 11) (h : KFactSmallIdent) :
    KFactSmallGammaSolvableSpor := by
  intro K _ _ hs hnab hc p hp hp2 T hT hΓ hAut hL hU hA hL34 hFi
  rcases isSmallStrongP_of_autRank h hs hnab hc hp hp2 T hT hΓ hAut with
    hK | hK | hK | ⟨rfl, hK | hK⟩ | ⟨rfl, hK | hK | hK⟩ | ⟨rfl, hK⟩
  · exact absurd hK hL
  · exact absurd hK hU
  · exact absurd hK hA
  · exact absurd ⟨rfl, hK⟩ hL34
  · exact (sporCore_m11 hK T).isSolvable_glbCore hp hΓ
  · exact (sporCore_of_isTitsGroup hs hnab hK T).isSolvable_glbCore hp hΓ
  · exact (sporCore_of_isMcL hs hnab hK T).isSolvable_glbCore hp hΓ
  · exact absurd ⟨rfl, hK⟩ hFi
  · exact (sporCore_of_d2HeisLocalAt hp (by norm_num) hJ4 hs hnab hK T).isSolvable_glbCore hp hΓ

end CFSG.AGLEmbedding
