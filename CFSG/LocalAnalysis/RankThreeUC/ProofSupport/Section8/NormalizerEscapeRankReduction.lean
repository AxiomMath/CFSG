module


public import CFSG.Open.LocalVocabulary


public section


namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.Section8.NormalizerEscapeRankReduction


open CFSG.Open


variable {G : Type} [Group G] [Finite G]


theorem one_le_pRank_of_dvd {p : ℕ} (hp : p.Prime) (H : Subgroup G)
    (h : p ∣ Nat.card H) : 1 ≤ CFSG.Open.pRank p H := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := H) p h
  have hog : orderOf (g : G) = p := by rw [Subgroup.orderOf_coe, hg]
  have hEcard : Nat.card (Subgroup.zpowers (g : G)) = p ^ 1 := by
    rw [Nat.card_zpowers, hog, pow_one]
  have hEle : Subgroup.zpowers (g : G) ≤ H := by
    rw [Subgroup.zpowers_le]; exact g.2
  have hEel : CFSG.Open.IsElemAbelian p (Subgroup.zpowers (g : G)) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 b.2
      apply Subtype.ext
      show (a : G) * b = b * a
      rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hog, pow_orderOf_eq_one,
        one_zpow]
  unfold CFSG.Open.pRank
  refine le_csSup ?_ ⟨_, hEle, hEel, hEcard⟩
  refine ⟨Nat.card G, ?_⟩
  rintro k ⟨F, -, -, hF⟩
  have h1 : p ^ k ≤ Nat.card G := by
    rw [← hF]; exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card F)
  exact (Nat.lt_pow_self hp.one_lt).le.trans h1


end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.Section8.NormalizerEscapeRankReduction
