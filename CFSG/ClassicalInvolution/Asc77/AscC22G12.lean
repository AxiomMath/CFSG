module

public import CFSG.ClassicalInvolution.Asc77.AscC22G10
public import CFSG.ClassicalInvolution.Asc77.AscC22G11
public import CFSG.ClassicalInvolution.Asc77.AscT7OZ

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace C22G

set_option linter.unusedSectionVars false

variable {p f : ℕ} [Fact p.Prime]


theorem c22_2_proved (h4 : Hyp22FourTwins p f) : C22_2 p f :=
  c22_2_of (hyp22Hyp51z p f)
    (hyp22Hyp51u_of_fourthTwin (twinSqAlphaRows_of_orth p (twinSqOrth_proved p))
      (hyp22FourthTwin_of_fourTwins h4))

theorem c22_7_of_layerNormAlpha_proved (hY : C22_layerNormAlpha p f) : C22_7 p f :=
  let hW := S22.hyp22SettingWyl_of_ab (S16.hyp22FourthTwinAb_proved p f)
  let h4 := T7V.hyp22FourTwins_of_wyl hW
  c22_7_of_layerNormAlpha
    (thmEWithSylow_of_nonToral f G2D4Models.g2NonToralGenerate_all) h4
    (T7V.hyp22Fuse_of_wyl hW) (c22_2_proved h4)
    (fun G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h => hW G Ω K K' K₃ z u₁ u₂ u₃ h.setting) hY

theorem c22_8Gen_of_layerNormAlpha (hY : C22_layerNormAlpha p f) : C22_8Gen p f :=
  c22_8Gen_of_c22_7 (c22_7_of_layerNormAlpha_proved hY)

end C22G

end CFSG.ClassicalInvolution.Asc77
