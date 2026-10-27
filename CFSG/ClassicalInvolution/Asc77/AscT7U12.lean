module

public import CFSG.ClassicalInvolution.Asc77.AscT7U9
public import CFSG.ClassicalInvolution.Asc77.AscT7U11

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

namespace T7U

variable {p f : ℕ} [Fact p.Prime]


theorem c25_16Even_of_E4 (h11 : C25_11E4 p f) (hres : Even f → C25_16inv p f) :
    Even f → C25_16 p f :=
  fun _ => c25_16_of_inv_even (c25_11_of_E4 h11) hres

end T7U


variable {p f : ℕ} [Fact p.Prime]

theorem thm7A_of_inputs₁₃_E4
    (hconn : C21_14_Y_conn_W p f)
    (hres : TwinSqOrth p) (h4 : Hyp22FourTwins p f) (hF : Hyp22Fuse p f)
    (hgen22 : C22_8Gen p f) (hZ : Hyp22ZStarCu p f) (hchain22 : C22_chainSettingX p f)
    (hchain23 : C23_chainX p f)
    (hcore : C24_9_core p f) (hbig : C24_8_big p f) (hpair : C24_pair p f)
    (h11 : T7U.C25_11E4 p f) (h16 : Even f → T7U.C25_16inv p f) : Thm7A p f :=
  thm7A_of_inputs₁₃_c16inv hconn hres h4 hF hgen22 hZ hchain22 hchain23 hcore hbig hpair
    (T7U.c25_11_of_E4 h11) h16

end CFSG.ClassicalInvolution.Asc77
