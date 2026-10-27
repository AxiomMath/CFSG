module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveExFinal
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveExInE7
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveExInE6

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

section Bound

theorem starPrime_of_gls3_of_classical
    (hGLS : ComponentClassification.CatLeaf.GLS3OddLieAutComponentsInput)
    (hPSUi : OddFivePSUInnerInput) (hU45 : OddFiveU45GraphInput)
    (hPSp : OddFiveSL2BoundFamilyInput .PSp)
    (hOO : OddFiveSL2BoundFamilyInput .POmegaOdd) (hOP : OddFiveSL2BoundFamilyInput .POmegaPlus)
    (hOM : OddFiveSL2BoundFamilyInput .POmegaMinus) {f : ℕ} (hf : 2 ≤ f) :
    StarPrimeStatement f :=
  starPrime_of_gls3_of_classical_exc hGLS hPSUi hU45 hPSp hOO hOP hOM
    (fun _ => e7InnerTwoPartInput (by norm_num) (by norm_num) (by norm_num))
    (fun _ => twistedE6InnerTwoPartInput (by norm_num) (by norm_num) (by norm_num)) hf

end Bound

end CFSG.SeitzReduction.RankOne
