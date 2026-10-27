module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp62BlockEscMSide
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.U62ThreeCentMain

public section

namespace CFSG.AGLEmbedding

theorem kFactU62ThreeCent : KFactU62ThreeCent := by
  intro L _ _ d hd he x hx
  exact U62ThreeCent.u62ThreeCent hd he hx

end CFSG.AGLEmbedding
