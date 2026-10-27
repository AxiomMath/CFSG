module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveListL45
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveListPSUGraph

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem oddFiveSL2ListFamilyInput_PSU_of_inner
    (hinner : OddFivePSUInnerInput) (h45 : OddFiveU45GraphInput) :
    OddFiveSL2ListFamilyInput .PSU :=
  oddFiveSL2ListFamilyInput_PSU_of_classes hinner (oddFivePSUGraphInput_of_U45 h45)

section Bound

theorem catSL2OddLieBound_two_of_eleven
    (hGLS : ComponentClassification.CatLeaf.GLS3OddLieAutComponentsInput)
    (hPSUi : OddFivePSUInnerInput) (hU45 : OddFiveU45GraphInput)
    (hPSp : OddFiveSL2BoundFamilyInput .PSp)
    (hOO : OddFiveSL2BoundFamilyInput .POmegaOdd) (hOP : OddFiveSL2BoundFamilyInput .POmegaPlus)
    (hOM : OddFiveSL2BoundFamilyInput .POmegaMinus) (hG2 : OddFiveSL2BoundFamilyInput .G2)
    (hF4 : OddFiveSL2BoundFamilyInput .F4) (hE6 : OddFiveSL2BoundFamilyInput .E6)
    (hE7 : OddFiveSL2BoundFamilyInput .E7) (hE8 : OddFiveSL2BoundFamilyInput .E8)
    (h2E6 : OddFiveSL2BoundFamilyInput .twistedE6)
    (h3D4 : OddFiveSL2BoundFamilyInput .trialityD4) : CatSL2OddLieBound 2 :=
  catSL2OddLieBound_two_of_twelve hGLS
    (oddFiveSL2BoundFamilyInput_of_list (oddFiveSL2ListFamilyInput_PSU_of_inner hPSUi hU45))
    hPSp hOO hOP hOM hG2 hF4 hE6 hE7 hE8 h2E6 h3D4

end Bound

end CFSG.SeitzReduction.RankOne
