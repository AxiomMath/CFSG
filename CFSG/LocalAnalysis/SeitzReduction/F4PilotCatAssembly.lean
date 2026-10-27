module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatSporadic

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)

theorem sp6CatalogueClauses_of_inputs (hEO : CatSp6EvenOuter)
    (hGLS : GLS3OddLieAutComponentsInput) (hX : Sp6NotOddLieInput) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hres : CatSp6SporadicResidual) :
    Sp6CatalogueClauses :=
  ⟨catSp6Alternating, catSp6EvenInner, hEO, catSp6OddLie_of_inputs hGLS hX,
    catSp6Sporadic_of_residual hMinn hMcomp hres, catSp6Covers⟩

end CFSG.SeitzReduction.F4Pilot
