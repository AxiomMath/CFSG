module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIIMult
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8Lemma83Mult

public section

namespace CFSG.ComponentClassification.RankTwoExcHypII

open CFSG.ComponentClassification.RankTwoStandard

theorem excEvenMultiplier :
    ExcEvenMultiplier := by
  intro A _ _ hA hT hev
  by_contra h
  simp only [not_or] at h
  obtain ⟨hG2, hF4, hE6⟩ := h
  exact (Nat.not_odd_iff_even.mpr hev)
    (RankTwoExceptional.odd_card_center_of_exc_type hA hT hG2 hF4 hE6)

end CFSG.ComponentClassification.RankTwoExcHypII
