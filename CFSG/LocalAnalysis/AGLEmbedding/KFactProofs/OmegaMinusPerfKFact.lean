module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp62BlockCMSmall
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusPerfMain

public section

namespace CFSG.AGLEmbedding

theorem kFactOmegaMinusThreePerfectCent : KFactOmegaMinusThreePerfectCent := by
  intro L _ _ m d hm hd he x hx
  exact OmegaMinusPerf.omegaMinusPerfectCent hm hd he hx

end CFSG.AGLEmbedding
