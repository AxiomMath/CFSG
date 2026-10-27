module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS2
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWGroup

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS GrS4

theorem l34EndStructureStep_of_inputs (hE2 : L34EndFusionStep)
    (hRest : L34EndStructureRestStep) : L34EndStructureStep := by
  intro G _ _ a x J S A hset hcent hZ hrun hZc hZ4 hQc hinv hSyl
  exact hRest G a x J S A hset hcent hZ hrun hZc hZ4 hQc hinv hSyl
    (hE2 G a x J S A hset hcent hZ hrun hZc hZ4 hQc hinv hSyl)

end CFSG.ComponentClassification.GrSLit
