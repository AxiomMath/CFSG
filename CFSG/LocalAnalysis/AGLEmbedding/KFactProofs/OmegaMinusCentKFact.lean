module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp62BlockEscMSide
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusCentThree

public section

namespace CFSG.AGLEmbedding

theorem kFactOmegaMinusFiveThreeCent : KFactOmegaMinusFiveThreeCent := by
  intro L _ _ d ⟨m, hm, hd⟩ he x hx
  exact OmegaMinusCent.omegaMinusThreeCent hm hd he hx

end CFSG.AGLEmbedding
