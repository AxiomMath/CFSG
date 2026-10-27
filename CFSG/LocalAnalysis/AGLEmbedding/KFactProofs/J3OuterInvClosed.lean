module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3OuterInv
public import CFSG.LocalAnalysis.AGLEmbedding.J3Target

public section

namespace CFSG.AGLEmbedding

theorem kFactJ3OuterInvolution :
    KFactJ3OuterInvolution :=
  kFactJ3OuterInvolution_of
    (kFactJ3OuterRank_closed CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv)

end CFSG.AGLEmbedding
