module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoCore
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNInputRed

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GNInputRed

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData


theorem rankTwo_holds : RankTwo := by
  intro X _ _ T hX _ T₁ T₂ hC Ls hY hcl
  exact RankTwoCore.not_rankOneChevTwo_of_gnParabolic hX
    (CFSG.AGLEmbeddingD2.Tits.GN516.agl81I516_of_graphOrbit
      CFSG.AGLEmbeddingD2.Tits.GN516.kFactChevGraphOrbit_proved
      CFSG.AGLEmbeddingD2.Tits.GN516.agl81I516SymOver_holds X T hX T₁ T₂ hC) hY
    (isChevTwo_of_classicalTwoOrG2 hcl)

end CFSG.LocalAnalysis.RankThreeUC.S15.GNInputRed
