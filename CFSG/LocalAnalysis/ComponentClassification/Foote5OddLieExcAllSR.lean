module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcAll
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcTwGraph
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcG2Three
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcRee
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcThree
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcSRD4

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem oddLieCoreFamilyInput_exceptional_of_E7_twistedE6
    (hE7 : InnerDiagCoreInput .E7) (hTE6i : TwistedE6InnerCoreInput) :
    ∀ τ : StatedLieTag, τ ∉ classicalTags → OddLieCoreFamilyInput τ :=
  (open Subgroup in oddLieCoreFamilyInput_exceptional (innerDiagThreeCoreInput_F4_E8 (Or.inl rfl))
      innerDiagThreeCoreInput_E6 (innerDiagThreeCoreInput_F4_E8 (Or.inr rfl)) g2ThreeInnerCoreInput
      g2ThreeOuterCoreInput e6GraphCoreInput hE7 hTE6i twistedE6GraphCoreInput
      trialityInnerCoreInput_holds smallReeInnerCoreInput)

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
