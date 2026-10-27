module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallGammaAlt
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallGammaLin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallGammaUnitary
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem kFactSmallGammaSolvableThree : KFactSmallGammaSolvableThree := by
  intro K _ _ _ _ _ T _ _ _ hcases
  rcases hcases with hA | hU | hL
  · obtain ⟨e⟩ := hA
    exact (KFactProofs.SmallGamma.smallGammaData_altSix e T).isSolvable_glbCore
  · exact (KFactProofs.SmallGamma.smallGammaData_isSmallUnitary hU T).isSolvable_glbCore
  · exact (KFactProofs.SmallGamma.smallGammaData_of_isLinThreeFour hL T).isSolvable_glbCore

end CFSG.AGLEmbedding
