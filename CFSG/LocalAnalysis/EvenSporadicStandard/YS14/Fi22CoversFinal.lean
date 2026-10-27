module

public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.Fi22Covers
public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.Fi23DSylow

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.YS14


theorem fi22Covers_of_multipliers
    (hSM : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers) :
    CFSG.EvenSporadicStandard.Induction.Fi.Fi22CoversFixesElem :=
  fi22Covers_of_fi23D hSM involutionFixesElem_fi23D

end CFSG.EvenSporadicStandard.YS14

end
