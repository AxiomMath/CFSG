module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7EM06
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7EN3
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7EN5

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7E.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 (FixesUniqueCoset)

section Assembly


theorem e18_6_proved : E18_6 :=
  AscE186.e18_6_of_wfree (fun _ _ _ _ _ _ _ _ _ c => c.hyp.cent)
    (fun _ _ _ _ _ _ _ _ _ c Gb _ _ hlt Ωb Kb Sb Rb Wb Hb hst ht hcn =>
      c.minimal Gb hlt Ωb Kb Sb Rb Wb Hb hst ⟨ht, hcn⟩)

theorem e18_7_proved : E18_7 :=
  e18_7 ⟨l6_7_proved, l6_9_proved, l6_11_proved, e18_6_proved⟩ e18_4C3

theorem e18_8z_proved : E18_8z :=
  e18_8z_of_e18_7 e18_7_proved

theorem e18_9_proved : E18_9 :=
  e18_9 (e18_3 l6_7_proved) e18_6_proved e18_7_proved (E189E4.of_e187 e18_4C3) e189Sect_proved

theorem minCexFalse_proved : MinCexFalse := by
  intro G _ _ Ω K S R W H c
  obtain ⟨z, hz1, -⟩ := c.exists_centralizer_le
  obtain ⟨S', W', c', hSyl⟩ := c.exists_config_sylow_centralizer hz1
  obtain ⟨-, hF⟩ := e18_6_proved G Ω K S' R W' H c'
  have hzc : FixesUniqueCoset z H := e18_8z_proved G Ω K S' R W' H c' z hz1
  exact e18_endS c' hF hz1 hSyl hzc fun h h1 h2 h3 =>
    e18_9_proved G Ω K S' R W' H c' z hz1 h h1 h2 h3

theorem thmEWithSylow_proved : ThmEWithSylow :=
  thmEWithSylow_of_minCexFalse minCexFalse_proved

end Assembly

end CFSG.ClassicalInvolution.Hat2A7E.Asc77

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.ClassicalInvolution.Asc77


theorem a7ThmE_proved : A7ThmE := fun G _ _ Ω K S R W H hst hH =>
  Hat2A7E.Asc77.thmEWithSylow_proved G Ω K S R W H (Hat2A7E.Asc77.EStand.ofA7 hst) hH

end CFSG.ClassicalInvolution.Hat2A7S
