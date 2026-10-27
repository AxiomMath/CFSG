module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25Bridge
public import CFSG.ClassicalInvolution.Q3.Q3T7P25W01
public import CFSG.ClassicalInvolution.ModelFacts.L6CFinal

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7P25

abbrev NC4Three : Prop := Q3T8.Asc77.C25X.NC4Fact

abbrev C25_9Three : Prop := Q3T8.Asc77.C25_9

abbrev C25_11Om5Three : Prop := Q3T8.Asc77.C25Y.C25_11Ω5

theorem c25_11Three_of_residuals (hnc4 : NC4Three) (h9 : C25_9Three) (hΩ5 : C25_11Om5Three) :
    C25_11Three :=
  Q3T8.Asc77.C25Y.c25_11_of_residuals hnc4 h9
    (CFSG.ClassicalInvolution.ModelFacts.L6C.layer6Cen4_proved (p := 3) (f := 1)) hΩ5

abbrev Layer5SqThree : Prop := Q3T8.Asc77.C25W.Layer5Sq

abbrev CentExtThree : Prop := Q3T8.Asc77.C25W.CentExt

theorem c25_9Three_of_residuals (hnc4 : NC4Three) (h5 : Layer5SqThree) (hExt : CentExtThree) :
    C25_9Three :=
  Q3T8.Asc77.C25W.c25_9_of_centExt hnc4
    (CFSG.ClassicalInvolution.ModelFacts.L6C.layer6Cen4_proved (p := 3) (f := 1)) h5 hExt

theorem c25_11Three_of_residuals4 (hnc4 : NC4Three) (h5 : Layer5SqThree) (hExt : CentExtThree)
    (hΩ5 : C25_11Om5Three) : C25_11Three :=
  c25_11Three_of_residuals hnc4 (c25_9Three_of_residuals hnc4 h5 hExt) hΩ5

theorem c25_E4Three_of_residuals4 (hnc4 : NC4Three) (h5 : Layer5SqThree) (hExt : CentExtThree)
    (hΩ5 : C25_11Om5Three) : Q3T7.C25_E4Three :=
  c25_E4Three_of_c25_11 (c25_11Three_of_residuals4 hnc4 h5 hExt hΩ5)

end CFSG.ClassicalInvolution.Q3.Q3T7P25
