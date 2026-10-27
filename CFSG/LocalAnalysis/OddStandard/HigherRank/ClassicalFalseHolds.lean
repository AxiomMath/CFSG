module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.ClassicalFalse
public import CFSG.LocalAnalysis.OddStandard.HigherRank.BlowUpA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.Triality.Member
public import CFSG.LocalAnalysis.ComponentClassification.KProperComponentLocalBLeavesHarris
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1OfCI
public import CFSG.LocalAnalysis.ComponentClassification.GS82L34P9
public import CFSG.LocalAnalysis.ComponentClassification.GS82CIInputsL34

public section

namespace CFSG.OddStandard.HigherRank

open CFSG.ComponentClassification CFSG.ComponentClassification.HarrisLit

section


theorem classicalFalse_of_ci
    (hCI : GSLit.ClassicalInvolutionInput)
    (hS : GSThmB.Solomon2AnInput) : ClassicalFalse :=
  have hT1 := T1.harris82Theorem1KProper_of_ci hCI
  have hID := KProperRelativeB.harris81Lemma35IdentFact_of_classical hCI
  classicalFalse RankTwoOddLie.oddLieInputs CFSG.LieType.HighestRoot.trialityD4SL2Unique
    TBLit.griessMultipliersAllModels_holds
    (L35.statement_holds_slTwo hT1
      (harris82Theorem3SLTwo_of_theorem1 hT1 TBLit.griessMultipliersAllModels_holds hID hCI) hID)
    hS (blowUpAFalse GS82PumpInputs.l34ExpFourPumpInput_holds (GSThmB.l34StandardInput_of_ci hCI))
    trialityD43Member_holds

end

end CFSG.OddStandard.HigherRank
