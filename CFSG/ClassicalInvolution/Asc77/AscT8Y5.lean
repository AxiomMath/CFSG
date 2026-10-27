module

public import CFSG.ClassicalInvolution.Asc77.AscT8Y4
public import CFSG.ClassicalInvolution.Asc77.AscT8S26NoF

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable {p f : ℕ} [Fact p.Prime]

theorem c27_8nE4_of_c27_YnE4 (h : C27_YnE4 p f) : C27_8nE4 p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hE4
  have hx : z * t * (z * t) = 1 :=
    T8.mul_self_zt hs.stand.odd hs.stand.hyp hs.hz hs.hJ hs.ht
  exact T8.centralizer_le_sigmaNorm_of_layerJoin_le hs
    ((T8.layerJoin_le_rLayer hs.stand.odd hs.stand.five hs.stand.hyp hx).trans
      (h G Ω K J S R T W z t hs hdisc hE4))

theorem c27_8E4_of_c27_YE4 (h : C27_YE4 p f) : C27_8E4 p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hE4
  have hx : z * t * (z * t) = 1 :=
    T8.mul_self_zt hs.stand.odd hs.stand.hyp hs.hz hs.hJ hs.ht
  exact T8.centralizer_le_sigmaNorm_of_layerJoin_le hs
    ((T8.layerJoin_le_rLayer hs.stand.odd hs.stand.five hs.stand.hyp hx).trans
      (h G Ω K J S R T W z t hs hdisc hE4))

theorem c27_8_of_core (hD4 : Ih8D4Star p f) (h2 : C27_2 p f) (hE : C27_8E4 p f)
    (h7 : C27_7ab p f) (hY : C27_Ysmall p f) : C27_8 p f :=
  c27_8_of_split hE (c27_8nE4_of_c27_YnE4 (c27_YnE4_of_core hD4 h2 h7 hY))

theorem thm8A_of_core (hD4 : Ih8D4Star p f) (h2 : C26_2 p f) (h13 : C26_13 p f)
    (hE : C27_8E4 p f) (h7 : C27_7ab p f) (hY : C27_Ysmall p f) : Thm8A p f :=
  thm8A_of_c26_2_c26_13 h2 h13 (c27_4a_of_min (c27_2_of_c26_2_c26_13 h2 h13) c27_4M_proved)
    (c27_8_of_core hD4 (c27_2_of_c26_2_c26_13 h2 h13) hE h7 hY)

end CFSG.ClassicalInvolution.Asc77
