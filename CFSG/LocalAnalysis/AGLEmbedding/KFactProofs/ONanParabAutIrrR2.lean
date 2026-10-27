module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrFinal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrG2Torus
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrSmall
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrR2Plus
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrR2MinusA
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrR2Uni

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

theorem orthPlusR2 : OrthPlusR2 := fun _ _ _ _ _ h _ => autScalarTorus_pomegaPlus h

theorem orthMinusR2 : OrthMinusR2 := fun _ _ _ _ _ h _ => autScalarTorus_pomegaMinus h

theorem uniR2 : UniR2 := fun _ _ _ _ _ h _ => autScalarTorus_psu h


theorem kFactParabolicAutomizerIrrPB : CFSG.AGLEmbedding.KFactParabolicAutomizerIrrPB :=
  irrPB_of_yLevel
      (yLevelIrr_of_inputs orthPlusR2 orthMinusR2 uniR2 yLevelIrrOn_isG2Two yLevelIrrOn_small)

end CFSG.AGLEmbedding.ParabAutIrr
