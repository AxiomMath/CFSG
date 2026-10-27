module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.FactsAtlasRest
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Fi22U62SubProof

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction.Fi


theorem FiAtlasRest.of_parts (h22 : Fi22CoversFixesElem) (hU : U62CoversFixesElem)
    (hodd : U62OddExclHered) : FiAtlasRest :=
  ⟨h22, hU, fi22U62Sub_proved, hodd⟩

end CFSG.EvenSporadicStandard.Induction.Fi
