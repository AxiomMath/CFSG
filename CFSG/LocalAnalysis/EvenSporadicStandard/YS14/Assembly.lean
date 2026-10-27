module

public import CFSG.Yardstones.M1442643da6f2.Definitions

public section

namespace CFSG.EvenSporadicStandard.YS14

open CFSG.Yardstones.M1442643da6f2

theorem fischerThompsonRowInputs_of_fields
    (hypOneFi24 : CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.HypothesisOne
      (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime))
    (fi22Covers : CFSG.EvenSporadicStandard.Induction.Fi.Fi22CoversFixesElem)
    (u62Covers : CFSG.EvenSporadicStandard.Induction.Fi.U62CoversFixesElem)
    (u62OddExcl : CFSG.EvenSporadicStandard.Induction.CITPart2 →
      CFSG.EvenSporadicStandard.Induction.Fi.U62OddExclHered)
    (thSylowWreathPair : CFSG.EvenSporadicStandard.ThStd.ThSylowWreathPair) :
    FischerThompsonRowInputs :=
  ⟨hypOneFi24, fi22Covers, u62Covers, u62OddExcl, thSylowWreathPair⟩

end CFSG.EvenSporadicStandard.YS14
