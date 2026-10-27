module

public import CFSG.ClassicalInvolution.Asc77.AscC22G6
public import CFSG.ClassicalInvolution.Asc77.AscC22G9
public import CFSG.ClassicalInvolution.Asc77.AscS16P

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace C22G

variable {p f : ℕ} [Fact p.Prime]


theorem c22_8Gen_of_alpha (h4 : Hyp22FourTwins p f) (hF : Hyp22Fuse p f) (h7 : C22_7 p f) :
    C22_8Gen p f :=
  c22_8Gen_of_layerStar (c22_layerStar_of_alpha h4 hF h7)

theorem c22_8Gen_of_c22_7 (h7 : C22_7 p f) : C22_8Gen p f :=
  let hW := S22.hyp22SettingWyl_of_ab (S16.hyp22FourthTwinAb_proved p f)
  c22_8Gen_of_alpha (T7V.hyp22FourTwins_of_wyl hW) (T7V.hyp22Fuse_of_wyl hW) h7

end C22G

end CFSG.ClassicalInvolution.Asc77
