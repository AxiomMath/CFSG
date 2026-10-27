module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6SmallArms
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClShapes
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaSmall
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSUSmall
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSpSmallMain
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmallMain
public import CFSG.LocalAnalysis.SeitzReduction.GLS3OddHolds

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank

section Inner


theorem oddA6Small_of_inputs (hO : CatLeaf.LieOrderFormulasInput) : ∀ t, OddA6Small t :=
  oddA6Small_all (oddA6Small_PSL hO) (oddA6Small_PSU hO) (oddA6Small_PSp hO) (oddA6Small_POmegaOdd hO) (oddA6Small_POmegaMinus hO)

theorem a6InnerLieSmall_holds : A6InnerLieSmall :=
  a6InnerLieSmall_of_classify
    (oddA6Shape_of_inputs CatLeafProof.lieOrderFormulasInput
      SeitzReduction.gls3OddLieAutComponentsInput)
    (oddA6Small_of_inputs CatLeafProof.lieOrderFormulasInput)

end Inner

section Outer


theorem a6OuterLieSmall_holds : A6OuterLieSmall :=
  a6OuterLieSmall_of_classify CatLeafProof.lieOrderFormulasInput
    (oddA6Shape_of_inputs CatLeafProof.lieOrderFormulasInput
      SeitzReduction.gls3OddLieAutComponentsInput)
    (oddA6Small_of_inputs CatLeafProof.lieOrderFormulasInput)

end Outer

end CFSG.ComponentClassification.CatFC
