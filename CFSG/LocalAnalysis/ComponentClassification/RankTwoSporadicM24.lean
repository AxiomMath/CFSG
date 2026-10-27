module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM24Check
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24
public import CFSG.Monster.Schur.M24

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M24

theorem sporadicCaseOdd_M24
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) :
    SporadicCaseOdd .M24 := by
  obtain ⟨_, _, _, _, _, _, _, h⟩ := m24_check
  exact sporadicCaseOdd_M24_ofC CFSG.Sporadic.Schreier.m24_center_eq_bot'
    (CFSG.Sporadic.Schreier.inner_eq_top_of_card_le CFSG.Sporadic.Schreier.m24_center_eq_bot'
      CFSG.Sporadic.Schreier.m24_mulAut_card)
    (oddMultiplier_of_noPerfectDoubleCover CFSG.Monster.Schur.noPerfectDoubleCover_nativeM24)
    h h32 h33

end CFSG.ComponentClassification.RankTwoSporadic.M24
