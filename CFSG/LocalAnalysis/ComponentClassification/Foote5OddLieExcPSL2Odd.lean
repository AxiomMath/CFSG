module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2Main
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2TwE6
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2D4

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof

theorem noPSLTwoOddCentreComponent_twistedE6 :
    NoPSLTwoOddCentreComponent .twistedE6 :=
  noPSLTwoOddCentreComponent_of_famInner lieOrderFormulasInput (by decide)
    (famInnerNoPSL2_twistedE6 lieOrderFormulasInput)

theorem noPSLTwoOddCentreComponent_trialityD4 :
    NoPSLTwoOddCentreComponent .trialityD4 :=
  noPSLTwoOddCentreComponent_of_famInner lieOrderFormulasInput (by decide)
    famInnerNoPSL2_trialityD4

theorem noPSLTwoOddCentreComponent_of_mem
    {t : StatedLieTag} (ht : t ∈ chevalleyExceptionalTags) : NoPSLTwoOddCentreComponent t := by
  simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact noPSLTwoOddCentreComponent_untwisted (Or.inl rfl)
  · exact noPSLTwoOddCentreComponent_untwisted (Or.inr (Or.inl rfl))
  · exact noPSLTwoOddCentreComponent_untwisted (Or.inr (Or.inr (Or.inl rfl)))
  · exact noPSLTwoOddCentreComponent_untwisted (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact noPSLTwoOddCentreComponent_untwisted (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  · exact noPSLTwoOddCentreComponent_twistedE6
  · exact noPSLTwoOddCentreComponent_trialityD4

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
