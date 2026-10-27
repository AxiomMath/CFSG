module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IStmt

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

theorem l411_zinsyl_of_steps (hb : L411ZIBoundStmt) (he : L411ZIE4Stmt) (h1 : L411ZI1Stmt) :
    L411ZInSylStmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau hG hB hz hs
  rcases hb hG hB hz hs with h | h
  · exact h1 hG hB hz hs h
  · exact he hG hB hz hs h

end CFSG.OddStandard.SmallF3.HarrisU33
