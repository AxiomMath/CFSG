module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltAut
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltAutThree

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem autFixInner_of_isAltTwoP (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : IsAltTwoP p K) (T : Sylow p K) : AutFixInner p K T := by
  by_cases h3 : p = 3
  · subst h3
    exact autFixInner_of_isAltTwoP_three hK T
  · have h4 : p ≠ 4 := by
      rintro rfl
      norm_num at hp
    have := hp.two_le
    exact autFixInner_of_isAltTwoP_of_five_le hp (by omega) hK T

theorem oneSmallFacts_of_isAltTwoP (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : IsAltTwoP p K) (T : Sylow p K) : OneSmallFacts p K T :=
  oneSmallFacts_of_localFacts hp (localFacts_of_isAltTwoP hp hp2 hK T)
    (autFixInner_of_isAltTwoP hp hp2 hK T) (autPInner_of_isAltTwoP hp hp2 hK)

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
