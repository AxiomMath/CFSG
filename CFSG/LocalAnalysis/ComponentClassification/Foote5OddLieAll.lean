module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcAllSR
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSLFam
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClUSplitIn
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClUBlockThree
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClUPaired
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClUGraph
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClSpFour
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOPlusFour

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem oddLieOuterCoreInput_of_E7_twistedE6
    (hE7 : Exc.InnerDiagCoreInput .E7) (hTE6i : Exc.TwistedE6InnerCoreInput) :
    OddLieOuterCoreInput := by
  refine oddLieOuterCoreInput_of_families fun τ => ?_
  by_cases hτ : τ ∈ classicalTags
  · simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact oddLieCoreFamilyInput_psl
    · exact oddLieCoreFamilyInput_psu_of (ClU.uSplitInput ClU.uBlockThreeGen) ClU.uPairedInput
        ClU.uGraphInput
    · exact oddLieCoreFamilyInput_psp
    · exact oddLieCoreFamilyInput_pomegaOdd
    · exact oddLieCoreFamilyInput_pomegaPlus
    · exact oddLieCoreFamilyInput_pomegaMinus
  · exact Exc.oddLieCoreFamilyInput_exceptional_of_E7_twistedE6 hE7 hTE6i τ hτ

end CFSG.ComponentClassification.Foote5.OddLieCore
