module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelectorResidual
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39

public section

namespace CFSG.EvenSmallLie.Child3

section Gap

theorem gapLagrangianSelector' : GapLagrangianSelector :=
  gapLagrangianSelector_of_psl39 SelL39.excluded_psl39

end Gap

end CFSG.EvenSmallLie.Child3
