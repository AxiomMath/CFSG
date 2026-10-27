module

public import CFSG.ClassicalInvolution.Asc77.AscT7W13
public import CFSG.ClassicalInvolution.Asc77.AscT7TInv
public import CFSG.ClassicalInvolution.Asc77.AscT7QMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77



variable {p f : ℕ} [Fact p.Prime]

theorem thm7A_of_inputs₁₃_even
    (hconn : C21_14_Y_conn_W p f)
    (hres : TwinSqOrth p) (h4 : Hyp22FourTwins p f) (hF : Hyp22Fuse p f)
    (hgen22 : C22_8Gen p f) (hZ : Hyp22ZStarCu p f) (hchain22 : C22_chainSettingX p f)
    (hchain23 : C23_chainX p f)
    (hcore : C24_9_core p f) (hbig : C24_8_big p f) (hpair : C24_pair p f)
    (h11 : C25_11 p f) (h16 : Even f → C25_16 p f) : Thm7A p f :=
  thm7A_of_inputs₁₃ hconn hres h4 hF hgen22 hZ hchain22 hchain23 hcore hbig hpair h11
    (T7T.c25_16_of_even_case h16) (T7Q.c25_20_ex_of_11_16 h11 (T7T.c25_16_of_even_case h16))

theorem thm7A_of_inputs₁₃_odd (hfo : Odd f)
    (hconn : C21_14_Y_conn_W p f)
    (hres : TwinSqOrth p) (h4 : Hyp22FourTwins p f) (hF : Hyp22Fuse p f)
    (hgen22 : C22_8Gen p f) (hZ : Hyp22ZStarCu p f) (hchain22 : C22_chainSettingX p f)
    (hchain23 : C23_chainX p f)
    (hcore : C24_9_core p f) (hbig : C24_8_big p f) (hpair : C24_pair p f)
    (h11 : C25_11 p f) : Thm7A p f :=
  thm7A_of_inputs₁₃_even hconn hres h4 hF hgen22 hZ hchain22 hchain23 hcore hbig hpair h11
    fun he => absurd he (Nat.not_even_iff_odd.mpr hfo)

end CFSG.ClassicalInvolution.Asc77
