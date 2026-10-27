module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S1111E4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S1111KBig

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Step1111K_of (hp : Asc82Pre11) (r : Asc82Res11a) (h119 : Asc82Lemma119)
    (h1110 : Asc82Lemma1110) (hKB : Asc82Step1111KBig) : Asc82Step1111K := by
  intro G _ _ t L S z K1 K2 T R hctx hP
  have hR : IsSylow2Of R (centralizer ({z} : Set G)) := h119 G t L S z K1 K2 T R hctx
  obtain ⟨hD, hdih⟩ := h1110 G t L S z K1 K2 T R hctx
  rcases sec11_isDih2_card hdih with h4 | h8
  · exact sec11_K_E4 hp hctx hR (sec11_strClosed_of_card_four hp r.l111N hctx h4)
  · exact hKB hp G t L S z K1 K2 T R hctx hR hD hdih h8 hP

end CFSG.OddStandard.SmallF3.Omega
