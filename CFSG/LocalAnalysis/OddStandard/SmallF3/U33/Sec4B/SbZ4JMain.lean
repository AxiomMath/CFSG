module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JG7C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IMain

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

theorem l411_zi1_holds : L411ZI1Stmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau hG _ hz hs hrel
  exact hz.z4j_false hG hs hrel

theorem l411_zinsyl_holds : L411ZInSylStmt :=
  l411_zinsyl_holds_of l411_zi1_holds

end CFSG.OddStandard.SmallF3.HarrisU33
