module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveExE6
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveExD4
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveListFinal
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TwoON

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

section Bound


theorem oddFiveSL2BoundFamilyInput_exc (hE7 : ∀ f, E7InnerTwoPartInput 5 f 5)
    (h2E6 : ∀ f, TwistedE6InnerTwoPartInput 5 f 5) :
    OddFiveSL2BoundFamilyInput .G2 ∧ OddFiveSL2BoundFamilyInput .F4 ∧
      OddFiveSL2BoundFamilyInput .E6 ∧ OddFiveSL2BoundFamilyInput .E7 ∧
        OddFiveSL2BoundFamilyInput .E8 ∧ OddFiveSL2BoundFamilyInput .twistedE6 ∧
          OddFiveSL2BoundFamilyInput .trialityD4 :=
  ⟨oddFiveSL2BoundFamilyInput_G2_F4_E8.1, oddFiveSL2BoundFamilyInput_G2_F4_E8.2.1,
    oddFiveSL2BoundFamilyInput_E6,
    oddFiveSL2BoundFamilyInput_of_twoPart (by decide) fun f =>
      excTwoPartInput_E7_of_inner (by norm_num) (by norm_num) (by norm_num) (hE7 f),
    oddFiveSL2BoundFamilyInput_G2_F4_E8.2.2, oddFiveSL2BoundFamilyInput_twistedE6_of_inner h2E6,
    oddFiveSL2BoundFamilyInput_trialityD4⟩

theorem catSL2OddLieBound_two_of_classical_exc
    (hGLS : ComponentClassification.CatLeaf.GLS3OddLieAutComponentsInput)
    (hPSUi : OddFivePSUInnerInput) (hU45 : OddFiveU45GraphInput)
    (hPSp : OddFiveSL2BoundFamilyInput .PSp)
    (hOO : OddFiveSL2BoundFamilyInput .POmegaOdd) (hOP : OddFiveSL2BoundFamilyInput .POmegaPlus)
    (hOM : OddFiveSL2BoundFamilyInput .POmegaMinus)
    (hE7 : ∀ f, E7InnerTwoPartInput 5 f 5) (h2E6 : ∀ f, TwistedE6InnerTwoPartInput 5 f 5) :
    CatSL2OddLieBound 2 :=
  have h := oddFiveSL2BoundFamilyInput_exc hE7 h2E6
  catSL2OddLieBound_two_of_eleven hGLS hPSUi hU45 hPSp hOO hOP hOM h.1 h.2.1 h.2.2.1 h.2.2.2.1
    h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2

theorem starPrime_of_gls3_of_classical_exc
    (hGLS : ComponentClassification.CatLeaf.GLS3OddLieAutComponentsInput)
    (hPSUi : OddFivePSUInnerInput) (hU45 : OddFiveU45GraphInput)
    (hPSp : OddFiveSL2BoundFamilyInput .PSp)
    (hOO : OddFiveSL2BoundFamilyInput .POmegaOdd) (hOP : OddFiveSL2BoundFamilyInput .POmegaPlus)
    (hOM : OddFiveSL2BoundFamilyInput .POmegaMinus)
    (hE7 : ∀ f, E7InnerTwoPartInput 5 f 5) (h2E6 : ∀ f, TwistedE6InnerTwoPartInput 5 f 5)
    {f : ℕ} (hf : 2 ≤ f) : StarPrimeStatement f :=
  starPrime_of_gls3_of_oddLie hGLS (catSL2OddLieBound_two_of_classical_exc hGLS hPSUi hU45 hPSp
    hOO hOP hOM hE7 h2E6) hf

end Bound

end CFSG.SeitzReduction.RankOne
