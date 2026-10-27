module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma310U
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma313

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

namespace Sec3

variable {L T : Subgroup G}

theorem lemma313_of_psu3
    (h : Sec3 G L T) (hF : Foundation) {f : ℕ} (hf : 2 ≤ f) (e : rankTwoQuot L ≃* PSU3 2 f) :
    Lemma313 L T (2 ^ f) := by
  obtain ⟨hT₁, hA₁, -⟩ := sylow_of_psu3 (odd_card_center_of_psu3 h.hyp.standard.1.1 hf e) hf e
    h.isSylowOf_T₁
  refine (h.facts_of_psu3 hF hf e).lemma313 h hF ?_
  rw [hT₁, hA₁]
  calc 2 ^ f = (2 ^ f) ^ 1 := (pow_one _).symm
    _ < (2 ^ f) ^ 3 := Nat.pow_lt_pow_right (Nat.one_lt_two_pow (by omega)) (by norm_num)

end Sec3

end CFSG.ComponentClassification.GMS78
