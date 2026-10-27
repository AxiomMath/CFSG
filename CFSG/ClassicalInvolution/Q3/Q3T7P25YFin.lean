module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25Fin
public import CFSG.ClassicalInvolution.Q3.Q3T7P25Y04

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7P25

abbrev ModelFacts3 : Prop := Q3T8.Asc77.C5O.ModelFacts

abbrev M8GFacts3 : Prop := Q3T8.Asc77.C5O.M8GFacts

theorem c25_11Om5Three_of_model_facts (hM : ModelFacts3) (hM8 : M8GFacts3) :
    C25_11Om5Three :=
  Q3T8.Asc77.C5O.c25_11Om5_of hM hM8

theorem c25_E4Three_of_model_facts4 (hnc4 : NC4Three) (h5 : Layer5SqThree) (hExt : CentExtThree)
    (hM : ModelFacts3) (hM8 : M8GFacts3) : Q3T7.C25_E4Three :=
  c25_E4Three_of_residuals4 hnc4 h5 hExt (c25_11Om5Three_of_model_facts hM hM8)

end CFSG.ClassicalInvolution.Q3.Q3T7P25
