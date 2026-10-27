module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveClSp
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveClOmega

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

section Bound

theorem oddFiveSL2BoundFamilyInput_PSp_holds : OddFiveSL2BoundFamilyInput .PSp :=
  oddFiveSL2BoundFamilyInput_of_list oddFiveSL2ListFamilyInput_PSp_holds

theorem oddFiveSL2BoundFamilyInput_POmegaOdd_holds : OddFiveSL2BoundFamilyInput .POmegaOdd :=
  oddFiveSL2BoundFamilyInput_of_list oddFiveSL2ListFamilyInput_POmegaOdd_holds

theorem oddFiveSL2BoundFamilyInput_POmegaPlus_holds : OddFiveSL2BoundFamilyInput .POmegaPlus :=
  oddFiveSL2BoundFamilyInput_of_list oddFiveSL2ListFamilyInput_POmegaPlus_holds

theorem oddFiveSL2BoundFamilyInput_POmegaMinus_holds : OddFiveSL2BoundFamilyInput .POmegaMinus :=
  oddFiveSL2BoundFamilyInput_of_list oddFiveSL2ListFamilyInput_POmegaMinus_holds

end Bound

end CFSG.SeitzReduction.RankOne
