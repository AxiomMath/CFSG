module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbCtx11
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbM4Stmt

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

theorem lemma4_11_of_steps (hI : Sec4Inputs) (h4 : L411FourStmt) (hQ : L411QStmt)
    (hS : L411SylStmt) (hA : L411AbStmt) : Lemma4_11Stmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau hG hB hc
  show (conjIn (ctxM t tau x₁ x₂) t).ncard ≠ 4
  intro hcard
  have ht2 : t * t = 1 := S4A.t_mul_self hc.hyp
  have hc' : Ctx10 t L S x₁ x₂ lam rho (t * tau) := ctx10_of_ctx4 hI hG (S4A.ctx4_swap hc.toCtx4)
  have hcard' : (conjIn (ctxM t (t * tau) x₁ x₂) t).ncard = 4 := by
    rw [S4B.ctxM_swap ht2]
    exact hcard
  have q := hQ hG hB (h4 hG hB hc hcard)
  have q' := hQ hG hB (h4 hG hB hc' hcard')
  rcases q.dich with hab | hsyl
  · exact hA hG hB q q' hab
  · exact hS hG hB q q' hsyl

end CFSG.OddStandard.SmallF3.HarrisU33
