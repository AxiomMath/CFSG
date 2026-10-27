module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallSylow
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroKFacts

public section

namespace CFSG.AGLEmbedding

open KFactProofs.SmallIdent

theorem kFactSmallSylowShape_of_smallIdent
    (h : KFactSmallIdent) : KFactSmallSylowShape := by
  intro K _ _ hs hnab hc p hp hp2 T hT hΓ hAut
  exact card_center_of_isSmallStrongP hp hp2 hs
    (isSmallStrongP_of_autRank h hs hnab hc hp hp2 T hT hΓ hAut)
    (rank_le_two_of_autRank hs hnab hp hAut) T

end CFSG.AGLEmbedding
