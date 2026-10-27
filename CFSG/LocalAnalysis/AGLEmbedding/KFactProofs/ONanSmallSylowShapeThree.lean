module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBasic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallM11
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeKFacts

public section

namespace CFSG.AGLEmbedding

open KFactProofs.SmallIdent

theorem kFactSmallSylowShapeThree_of_smallIdent
    (h : KFactSmallIdent) : KFactSmallSylowShapeThree := by
  intro K _ _ hs hnab hc T hT hΓ hAut hU
  have hK := isSmallStrongP_of_autRank h hs hnab hc Nat.prime_three (by norm_num) T hT hΓ hAut
  rcases hK with hL | hU' | hA | ⟨-, hL34 | hM⟩ | ⟨h5, -⟩ | ⟨h11, -⟩
  · exact sylowSq_of_isSmallLinTwo Nat.prime_three (by norm_num) hL T
  · exact absurd hU' hU
  · exact sylowSq_of_isAltTwoP Nat.prime_three (by norm_num) hA T
  · exact sylowSq_of_isLinThreeFour hL34 T
  · exact sylowSq_of_isM11 hM T
  · omega
  · omega

end CFSG.AGLEmbedding
