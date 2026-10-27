module

public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.Assembly
public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.HypOneFi24
public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.Fi22CoversFinal

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.YS14


theorem fischerThompsonRowInputs_of_hard_fields
    (hSM : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers)
    (u62Covers : CFSG.EvenSporadicStandard.Induction.Fi.U62CoversFixesElem)
    (u62OddExcl : CFSG.EvenSporadicStandard.Induction.CITPart2 →
      CFSG.EvenSporadicStandard.Induction.Fi.U62OddExclHered)
    (thSylowWreathPair : CFSG.EvenSporadicStandard.ThStd.ThSylowWreathPair) :
    CFSG.Yardstones.M1442643da6f2.FischerThompsonRowInputs :=
  fischerThompsonRowInputs_of_fields hypothesisOne_fi24Prime (fi22Covers_of_multipliers hSM)
    u62Covers u62OddExcl thSylowWreathPair

end CFSG.EvenSporadicStandard.YS14

end
