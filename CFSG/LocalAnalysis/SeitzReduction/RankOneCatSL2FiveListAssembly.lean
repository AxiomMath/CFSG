module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveListOrth

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

section Bound

theorem catSL2OddLieBound_two_of_remaining (hGLS : GLS3OddLieAutComponentsInput)
    (hsplit : OddFiveL45SplitInput)
    (hPSU : OddFiveSL2BoundFamilyInput .PSU) (hPSp : OddFiveSL2BoundFamilyInput .PSp)
    (hOO : OddFiveSL2BoundFamilyInput .POmegaOdd) (hOP : OddFiveSL2BoundFamilyInput .POmegaPlus)
    (hOM : OddFiveSL2BoundFamilyInput .POmegaMinus) (hG2 : OddFiveSL2BoundFamilyInput .G2)
    (hF4 : OddFiveSL2BoundFamilyInput .F4) (hE6 : OddFiveSL2BoundFamilyInput .E6)
    (hE7 : OddFiveSL2BoundFamilyInput .E7) (hE8 : OddFiveSL2BoundFamilyInput .E8)
    (h2E6 : OddFiveSL2BoundFamilyInput .twistedE6)
    (h3D4 : OddFiveSL2BoundFamilyInput .trialityD4) : CatSL2OddLieBound 2 :=
  catSL2OddLieBound_two_of_boundFamilies hGLS fun t => by
    cases t
    exacts [oddFiveSL2BoundFamilyInput_of_list (oddFiveSL2ListFamilyInput_PSL_of_split hsplit),
      hPSU, hPSp, hOO, hOP, hOM, hG2, hF4, hE6, hE7, hE8, h2E6, h3D4,
      oddFiveSL2BoundFamilyInput_of_list oddFiveSL2ListFamilyInput_twistedB2,
      oddFiveSL2BoundFamilyInput_of_list oddFiveSL2ListFamilyInput_twistedG2,
      oddFiveSL2BoundFamilyInput_of_list oddFiveSL2ListFamilyInput_twistedF4,
      oddFiveSL2BoundFamilyInput_of_list oddFiveSL2ListFamilyInput_Tits]

end Bound

end CFSG.SeitzReduction.RankOne
