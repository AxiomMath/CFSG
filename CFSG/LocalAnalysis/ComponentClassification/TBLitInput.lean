module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitTheorem

public section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.Blueprint

theorem thompsonBurgoyneInput_of_inputs
    (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Catalog)
    (hCI : StandardRecognition.ClassicalInvolutionTheoremModels) (hA : BurgoynePropA)
    (hB : BurgoynePropB) (hC : BurgoynePropC) (hL34 : L34PumpUpExclusion)
    (hSol : SolomonSignalizerInput) (hHe : HeldTrivialMultiplier)
    (hGA : GriessMultipliersAllModels) (hGC : GriessMultipliersCentralCovers) :
    GSLit.ThompsonBurgoyneInput :=
  fun X _ _ _ hnonab hK hz hU x y L hT =>
    thompson_burgoyne_of_inputs hUc hSch hCI hA hB hC hL34 hSol hHe hGA hGC X hnonab hK hz hU x y L
      hT

end CFSG.ComponentClassification.TBLit
