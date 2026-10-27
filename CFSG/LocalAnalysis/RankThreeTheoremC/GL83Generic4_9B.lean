module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9BNormal
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9BLayer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

theorem gl83Generic4_9B_holds : GL83Generic4_9B := by
  intro hInn hWC p _ Y _ _ S R Γ x hH
  by_cases h : CFSG.pCore p Y = ⊥
  · exact gl83Generic4_9BLayer_holds hInn hWC hH h
  · exact gl83Generic4_9BNormal_holds hH h

end CFSG.LocalAnalysis.RankThreeTheoremC
