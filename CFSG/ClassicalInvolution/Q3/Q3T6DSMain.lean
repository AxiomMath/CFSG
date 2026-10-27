module

public import CFSG.ClassicalInvolution.Q3.Q3T6DSOrb
public import CFSG.ClassicalInvolution.Q3.Q3T6DSC3
public import CFSG.ClassicalInvolution.Q3.Q3T6DC7
public import CFSG.ClassicalInvolution.Q3.Q3T6DSetupB
public import CFSG.ClassicalInvolution.Q3.Q3T6D8
public import CFSG.ClassicalInvolution.Q3.Q3T6DR10bMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

section Main

theorem c20_3_of_hyp51Three (hH : Res20_7Hyp51Three) : C20_3Three := by
  intro G _ _ _ K K' J S R R' W V z t d
  have hex : Hex20 (CoreAssembly.conjClass K) K J W := hexAll3 G K K' J S R R' W V z t d
  exact d.concl20_3_of_mod hex
    (res20_7NoC3_of_hyp51Three hH G K K' J S R R' W V z t d (d.concl20_4_of_hex hex))

theorem c20_5_of_hyp51Three (hH : Res20_7Hyp51Three) : C20_5Three :=
  c20_5_of_res20_7Three (res20_7_of_hyp51Three hH)

theorem c20_3_of_hyp51AtThree (hH : Res20_7Hyp51AtThree) : C20_3Three :=
  c20_3_of_hyp51Three (res20_7Hyp51_of_atThree hH)

theorem c20_5_of_hyp51AtThree (hH : Res20_7Hyp51AtThree) : C20_5Three :=
  c20_5_of_hyp51Three (res20_7Hyp51_of_atThree hH)

theorem t3CaseII3_of_hyp51At (hH : Res20_7Hyp51AtThree) (hP1 : Res10bP1Three) : T3CaseII3 :=
  t3CaseII3_of_steps sec20Setup3_proved (c20_3_of_hyp51AtThree hH) c20_4Three
    (c20_5_of_hyp51AtThree hH) c20_7Three c20_8Three (c20_10b_of_P1Three hP1)

end Main

end CFSG.ClassicalInvolution.Q3.Q3T6D
