module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25V03
public import CFSG.ClassicalInvolution.Q3.Q3T7P25YFin

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7P25

abbrev ParityE4Three : Prop := Q3T8.Asc77.CX.ParityE4

theorem centExtThree_of_parityE4 (hnc4 : NC4Three) (h5 : Layer5SqThree)
    (hT : Q3T8.Asc77.CX.LayerTwinFactsFive3) (hP : ParityE4Three) : CentExtThree := by
  have : Q3T8.Asc77.CX.Facts25V := ⟨by intros; exact hnc4, by intros; exact h5, hT⟩
  exact Q3T8.Asc77.CX.centExt_of_parityE4 hP

theorem c25_E4Three_of_model_facts6 (hnc4 : NC4Three) (h5 : Layer5SqThree)
    (hT : Q3T8.Asc77.CX.LayerTwinFactsFive3) (hP : ParityE4Three) (hM : ModelFacts3)
    (hM8 : M8GFacts3) : Q3T7.C25_E4Three :=
  c25_E4Three_of_model_facts4 hnc4 h5 (centExtThree_of_parityE4 hnc4 h5 hT hP) hM hM8

end CFSG.ClassicalInvolution.Q3.Q3T7P25
