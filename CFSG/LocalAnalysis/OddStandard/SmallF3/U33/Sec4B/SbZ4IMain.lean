module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IGlue
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4I0F
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR6B

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

theorem l411_zi_e4_holds : L411ZIE4Stmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau hG _ hz hs hrel
  exact hz.z4i_e4_false hG hs hrel

theorem l411_zinsyl_holds_of (h1 : L411ZI1Stmt) : L411ZInSylStmt :=
  l411_zinsyl_of_steps l411_zi_bound_holds l411_zi_e4_holds h1

end CFSG.OddStandard.SmallF3.HarrisU33
