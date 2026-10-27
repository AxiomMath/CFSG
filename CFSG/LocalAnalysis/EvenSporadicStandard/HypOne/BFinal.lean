module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.BD3Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.BNoOrder68

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HypOne.BabyHyp

open CFSG.Blueprint.NativeSporadic CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977


theorem hypothesisOne_B (h68 : BabyNoOrder68) : HypothesisOne (Carrier .B) :=
  hypothesisOne_B_of_roots babyRootClassLarge_two (babyRootClassLarge_three_of_noOrder68 h68)

end CFSG.EvenSporadicStandard.HypOne.BabyHyp
