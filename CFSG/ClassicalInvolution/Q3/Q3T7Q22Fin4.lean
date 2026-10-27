module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q22Fin3
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22H51uD

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected


theorem hyp22FourthTwin_proved [Fact Q3T7E.ThmEWithSylow3] [Fact Q3T8.Asc77.Hyp22Hyp51z]
    [Fact Q3T8.Asc77.S16.M11NoInverted3] : Q3T8.Asc77.Hyp22FourthTwin :=
  Q3T8.Asc77.S22.hyp22FourthTwin_of_ab Q3T8.Asc77.S16.hyp22FourthTwinAb_proved

theorem c22_1Three_of_rows (hE : Q3T7E.ThmEWithSylow3)
    (hrows : TwinSqAlphaAll3) (hEx : Q3T8.Asc77.ExactMembersHyp22) : C22_1Three := by
  have : Fact Q3T7E.ThmEWithSylow3 := ⟨hE⟩
  have : Fact Q3T8.Asc77.Hyp22Hyp51z := ⟨hyp22Hyp51z_proved⟩
  have : Fact Q3T8.Asc77.S16.M11NoInverted3 := ⟨Q3T8.Asc77.S16.m11NoInverted3_proved⟩
  exact c22_1Three_of_ex hE (hyp22Hyp51u_of_fourthTwin3 hrows hyp22FourthTwin_proved) hEx

end CFSG.ClassicalInvolution.Q3.Q3T7
