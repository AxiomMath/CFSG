module

public import CFSG.ClassicalInvolution.Asc77.AscT7U8
public import CFSG.ClassicalInvolution.Asc77.AscT7QMain
public import CFSG.ClassicalInvolution.Asc77.AscT7TOdd
public import CFSG.ClassicalInvolution.Asc77.AscT7W13

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

namespace T7U

variable {p f : ℕ} [Fact p.Prime]


theorem c25_16_of_inv_even (h11 : C25_11 p f) (hres : Even f → C25_16inv p f) : C25_16 p f :=
  (Nat.even_or_odd f).elim (fun he => c25_16_of_inv h11 (hres he)) T7T.c25_16_of_odd

end T7U


variable {p f : ℕ} [Fact p.Prime]

theorem thm7A_of_inputs₁₃_c16inv
    (hconn : C21_14_Y_conn_W p f)
    (hres : TwinSqOrth p) (h4 : Hyp22FourTwins p f) (hF : Hyp22Fuse p f)
    (hgen22 : C22_8Gen p f) (hZ : Hyp22ZStarCu p f) (hchain22 : C22_chainSettingX p f)
    (hchain23 : C23_chainX p f)
    (hcore : C24_9_core p f) (hbig : C24_8_big p f) (hpair : C24_pair p f)
    (h11 : C25_11 p f) (h16 : Even f → T7U.C25_16inv p f) : Thm7A p f :=
  thm7A_of_inputs₁₃ hconn hres h4 hF hgen22 hZ hchain22 hchain23 hcore hbig hpair h11
    (T7U.c25_16_of_inv_even h11 h16)
    (T7Q.c25_20_ex_of_11_16 h11 (T7U.c25_16_of_inv_even h11 h16))

end CFSG.ClassicalInvolution.Asc77
