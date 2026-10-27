module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgClass
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgF4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgRank4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

section Final


theorem l154NonCfgOutdiag_of_residuals (hF4 : L154F4Models) (hR4 : L154Rank4Models) :
    L154NonCfgOutdiag :=
  l154NonCfgOutdiag_of_models (l154NonCfgModels_of_residuals hF4 hR4)

theorem l154NonCfgOutdiag_holds : L154NonCfgOutdiag :=
  l154NonCfgOutdiag_of_residuals l154F4Models_holds l154Rank4Models_holds

end Final

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
