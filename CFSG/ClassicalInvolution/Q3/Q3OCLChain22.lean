module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q22Fin4
public import CFSG.ClassicalInvolution.Q3.Q3OCLExact

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3OCL


theorem exactMembersHyp22_proved [Fact Q3T7E.ThmEWithSylow3] [Fact Q3T8.Asc77.Hyp22Hyp51z]
    [Fact Q3T8.Asc77.Hyp22Hyp51u] [Fact Q3T8.Asc77.S16.M11NoInverted3]
    [Fact Q3T8.Asc77.C22G.PsuLayerApi3] : Q3T8.Asc77.ExactMembersHyp22 := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h
  have hs := h.setting
  have hWyl := Q3T8.Asc77.S22.hyp22SettingWyl_of_ab Q3T8.Asc77.S16.hyp22FourthTwinAb_proved
  have hW := hWyl G Ω K K' K₃ z u₁ u₂ u₃ hs
  have hG := Q3T8.Asc77.C22G.c22_8Gen_proved G Ω K K' K₃ z u₁ u₂ u₃ h
  have hα := Q3T8.Asc77.C22N.alpha_eq_bot_neg (by norm_num) hs hW hG
  exact exactMembers_of_alpha_22 hs hα

theorem c22_1Three_of_rows_noEx (hE : Q3T7E.ThmEWithSylow3)
    (hrows : Q3T7.TwinSqAlphaAll3) : Q3T7.C22_1Three := by
  have h1 : Fact Q3T7E.ThmEWithSylow3 := ⟨hE⟩
  have h2 : Fact Q3T8.Asc77.Hyp22Hyp51z := ⟨Q3T7.hyp22Hyp51z_proved⟩
  have h3 : Fact Q3T8.Asc77.S16.M11NoInverted3 := ⟨Q3T8.Asc77.S16.m11NoInverted3_proved⟩
  have h4 : Fact Q3T8.Asc77.Hyp22Hyp51u :=
    ⟨Q3T7.hyp22Hyp51u_of_fourthTwin3 hrows Q3T7.hyp22FourthTwin_proved⟩
  have h5 : Fact Q3T8.Asc77.C22G.PsuLayerApi3 := ⟨Q3T7.psuLayerApi3_proved⟩
  exact Q3T7.c22_1Three_of_rows hE hrows exactMembersHyp22_proved

end CFSG.ClassicalInvolution.Q3.Q3OCL
