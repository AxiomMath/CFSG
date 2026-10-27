module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveE
public import CFSG.LocalAnalysis.ComponentClassification.TBLitTheorem

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG

theorem thompsonBurgoyneTypes_of_inputs
    (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hCI : StandardRecognition.ClassicalInvolutionTheoremModels) (hA : TBLit.BurgoynePropA)
    (hB : TBLit.BurgoynePropB) (hC : TBLit.BurgoynePropC) (hL34 : TBLit.L34PumpUpExclusion)
    (hSol : TBLit.SolomonSignalizerInput) (hHe : TBLit.HeldTrivialMultiplier)
    (hGA : TBLit.GriessMultipliersAllModels) (hGC : TBLit.GriessMultipliersCentralCovers) :
    ThompsonBurgoyneTypes := fun X _ _ _ hnonab hK hz hU x y L hT =>
  TBLit.thompson_burgoyne_of_inputs hUc hSch hCI hA hB hC hL34 hSol hHe hGA hGC X hnonab hK hz hU
    x y L hT

theorem signalizerFivePumpTBInput_of_inputs
    (hbal : Sol78.BalanceTwoComponentInput) (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hCI : StandardRecognition.ClassicalInvolutionTheoremModels) (hA : TBLit.BurgoynePropA)
    (hB : TBLit.BurgoynePropB) (hC : TBLit.BurgoynePropC) (hL34 : TBLit.L34PumpUpExclusion)
    (hSol : TBLit.SolomonSignalizerInput) (hHe : TBLit.HeldTrivialMultiplier)
    (hGA : TBLit.GriessMultipliersAllModels) (hGC : TBLit.GriessMultipliersCentralCovers) :
    SignalizerFivePumpTBInput :=
  signalizerFivePumpTBInput_of_types hbal
    (thompsonBurgoyneTypes_of_inputs hUc hSch hCI hA hB hC hL34 hSol hHe hGA hGC)

end CFSG.ComponentClassification.SolMax
