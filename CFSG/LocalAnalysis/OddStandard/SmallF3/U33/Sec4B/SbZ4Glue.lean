module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4Stmt

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

theorem l411_ab_of_steps (h0 : L411ZSetupStmt) (h1 : L411ZInSylStmt) (h2 : L411ZNotSylStmt) :
    L411AbStmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau hG hB hq hq' hab
  rcases h0 hG hB hq hq' hab with hz | hz
  · by_cases hs : IsSylowIn 2 (ctxQ t tau x₁ x₂ rho) (ctxCQ t tau x₁ x₂ rho)
    · exact h1 hG hB hz hs
    · exact h2 hG hB hz hs
  · by_cases hs : IsSylowIn 2 (ctxQ t (t * tau) x₁ x₂ rho) (ctxCQ t (t * tau) x₁ x₂ rho)
    · exact h1 hG hB hz hs
    · exact h2 hG hB hz hs

end CFSG.OddStandard.SmallF3.HarrisU33
