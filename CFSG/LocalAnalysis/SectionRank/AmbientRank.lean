module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.SectionRank

variable {G : Type*} [Group G] [Finite G]

theorem pRank_coe_eq_openPRank (p : ℕ) (H : Subgroup G) :
    CFSG.pRank p H = CFSG.Open.pRank p H :=
  (pRank_eq_open_pRank_top p H).trans (pRank_eq_pRank_top_subgroup H).symm

theorem pRank_coe_eq_assemblyPRank (p : ℕ) (H : Subgroup G) :
    CFSG.pRank p H = CFSG.Assembly.pRank p H :=
  pRank_coe_eq_openPRank p H

theorem assembly_evenRank_eq_twoLocalOddRank (G : Type*) [Group G] [Finite G] :
    CFSG.Assembly.evenRank G = CFSG.twoLocalOddRank G := by
  refine le_antisymm (csSup_le' ?_) (csSup_le' ?_)
  · rintro _ ⟨q, H, hq, hq2, hH, rfl⟩
    by_cases hqG : q ∣ Nat.card G
    · refine le_csSup ⟨Nat.card G, ?_⟩
        ⟨H, hH, q, hq, hq2, hqG, (pRank_coe_eq_assemblyPRank q H).symm⟩
      rintro _ ⟨K, -, q', hq', -, -, rfl⟩
      rw [pRank_coe_eq_openPRank]
      exact pRank_le_card_of_one_lt hq'.one_lt K
    · obtain ⟨E, -, -, hE⟩ := exists_pRank hq.one_lt H
      have hdvd : q ^ CFSG.Open.pRank q H ∣ Nat.card G := hE ▸ Subgroup.card_subgroup_dvd_card E
      have h0 : CFSG.Open.pRank q H = 0 := by
        by_contra h0
        exact hqG ((dvd_pow_self q h0).trans hdvd)
      change CFSG.Open.pRank q H ≤ _
      rw [h0]
      exact Nat.zero_le _
  · rintro _ ⟨H, hH, q, hq, hq2, -, rfl⟩
    rw [pRank_coe_eq_assemblyPRank]
    exact le_csSup ⟨Nat.card G, by
        rintro _ ⟨q', K, hq', -, -, rfl⟩
        exact pRank_le_card_of_one_lt hq'.one_lt K⟩
      ⟨q, H, hq, hq2, hH, rfl⟩

end CFSG.SectionRank
