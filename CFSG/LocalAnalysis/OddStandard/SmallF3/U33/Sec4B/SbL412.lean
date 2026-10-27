module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP12h
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbStmt2

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

theorem lemma4_12 : Lemma4_12Stmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau hc
  exact ⟨S4B.l12_a hc, S4B.l12_b hc⟩

end CFSG.OddStandard.SmallF3.HarrisU33
