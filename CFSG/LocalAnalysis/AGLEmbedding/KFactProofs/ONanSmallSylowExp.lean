module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallSylow
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneKFacts

public section

namespace CFSG.AGLEmbedding

open KFactProofs.SmallIdent

theorem kFactSmallSylowExp_of_smallIdent
    (h : KFactSmallIdent) : KFactSmallSylowExp := by
  intro K _ _ hs hnab hc p hp hp2 T hT hΓ hAut t ht
  exact pow_eq_one_of_isSmallStrongP hp hp2 hs
    (isSmallStrongP_of_autRank h hs hnab hc hp hp2 T hT hΓ hAut) T hT t ht

end CFSG.AGLEmbedding
