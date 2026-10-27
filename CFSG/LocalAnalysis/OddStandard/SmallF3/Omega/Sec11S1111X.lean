module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S1111E4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S1111BigX

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Step1111X_of (hp : Asc82Pre11) (r : Asc82Res11a) (h119 : Asc82Lemma119)
    (h1110 : Asc82Lemma1110) (hB4 : Asc82InputDihSd) : Asc82Step1111X := by
  intro G _ _ t L S z K1 K2 T R hctx
  have hR : IsSylow2Of R (centralizer ({z} : Set G)) := h119 G t L S z K1 K2 T R hctx
  have hdih : IsDih2 (Subgroup.closure (secTheta t z R)) :=
    (h1110 G t L S z K1 K2 T R hctx).2
  rcases sec11_isDih2_card hdih with h4 | h8
  · exact sec11_X_E4 hp r.l111N hctx hR (sec11_strClosed_of_card_four hp r.l111N hctx h4)
  · exact sec11_X_big hp r.l111N hB4 hctx hR hdih h8

end CFSG.OddStandard.SmallF3.Omega
