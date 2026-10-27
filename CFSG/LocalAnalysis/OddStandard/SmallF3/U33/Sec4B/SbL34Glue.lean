module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Stmt

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

theorem l411_syl_of_steps (h0 : L34S0Stmt) (h1 : L34S1Stmt) (h2 : L34S2Stmt) (h3 : L34S3Stmt)
    (h4 : L34S4Stmt) (h5 : L34S5Stmt) (h6 : L34S6Stmt) : L411SylStmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau hG hB hq hq' hsyl
  have hL := h0 hG hB hq hq' hsyl
  obtain ⟨W, v, hv⟩ := h1 hG hB hL
  have hA := h2 hG hB hL
  have hP := h3 hG hB hA hv
  have hQ := h4 hG hB hP
  obtain ⟨ω, hω, hn⟩ := h5 hG hB hP hQ
  exact h6 hG hB hL hv ω hω hn

end CFSG.OddStandard.SmallF3.HarrisU33
