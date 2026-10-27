module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecLiftX1Six
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecLiftX1Setting
public import CFSG.LocalAnalysis.RankThreeUC.GN15Solv

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem jOutSupGuard_of_jOutCentral (hJ : JOutCentral) : JOutSupGuard :=
  fun _ _ _ T hX L _ _ _ hLn => hJ ↥(L ⊔ T) (T.subgroupOf (L ⊔ T)) (gnSetting_sup_of_normal hX hLn)

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15

end
