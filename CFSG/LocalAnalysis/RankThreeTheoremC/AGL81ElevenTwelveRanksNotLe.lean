module

import CFSG.RankThree.PartTwo.Census.Carrier.SpinDBridge
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194OmegaPlanes
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ICitedHyp111K

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TwelveRanksNotLe

theorem pRank_top_le_of_not_dvd_card {G : Type} [Group G] [Finite G] {p k : ℕ} (hp : p.Prime)
    (h : ¬ p ^ (k + 1) ∣ Nat.card G) : Open.pRank p (⊤ : Subgroup G) ≤ k := by
  by_contra hk
  obtain ⟨E, -, -, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup G)
  refine h ((pow_dvd_pow p (not_le.1 hk)).trans ?_)
  rw [← hcard]
  exact Subgroup.card_subgroup_dvd_card E

theorem four_le_pRank_three_of_isLieOver_D {Y : Type} [Group Y] [Finite Y] {r : ℕ}
    (h : IsLieOver Y (.D r) 2 1) : 4 ≤ Open.pRank 3 (⊤ : Subgroup Y) := by
  obtain ⟨⟨d, hv⟩, ⟨q, hqp, -, hd⟩, ⟨e⟩⟩ := h
  simp only at hd
  subst hd
  obtain ⟨⟨-, hf, hr⟩, K, hKf, hKfin, hK, ⟨e'⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hqp e
  rw [hqp] at hK
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have hr4 : 4 ≤ r := hr
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e']
  exact CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven.four_le_pRank_three_omegaPlus
    hr4

end TwelveRanksNotLe

end CFSG.LocalAnalysis.RankThreeTheoremC
