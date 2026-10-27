module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3Selector
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelK3Spor
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelOmega
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelK3Classical
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelExcSource
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelU43

public section

namespace CFSG.EvenSmallLie.Child3

section Residual

theorem residualExclusions_of_psl39 (hL39 : ExcludedLie .PSL 3 3 2) : ResidualExclusions :=
  ⟨SelK3.sporadicExclusions, orthogonalExclusions, classicalExclusions,
    SelExc.exceptionalExclusions, ⟨excluded_psu33, SelU43.excluded_psu43, hL39⟩⟩

end Residual

section Gap

theorem gapLagrangianSelector_of_psl39 (hL39 : ExcludedLie .PSL 3 3 2) :
    GapLagrangianSelector :=
  gapLagrangianSelector (residualExclusions_of_psl39 hL39)

end Gap

end CFSG.EvenSmallLie.Child3
