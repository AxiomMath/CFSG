module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaList3
import CFSG.GH74.KGroups.A6
import CFSG.GH74.KGroups.A7
import CFSG.Sporadic.Bridge.M22
import CFSG.Monster.B.TwoA.Fischer.M22Aut
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG CFSG.Open

theorem card_dvd_of_isPGroup_mulAut_of_perfect {K : Type} [Group K] [Finite K]
    [Group.IsPerfect K] {p n : ℕ} (hp : p.Prime)
    (hn : Nat.card (MulAut (K ⧸ Subgroup.center K)) = n) (B : Subgroup (MulAut K))
    (hB : IsPGroup p B) : ∃ k : ℕ, Nat.card B = p ^ k ∧ p ^ k ∣ n := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hB
  refine ⟨k, hk, ?_⟩
  have hinj := ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective K
  rw [← hk, ← Subgroup.card_map_of_injective hinj, ← hn]
  exact Subgroup.card_subgroup_dvd_card _

theorem smallAut_conclusion {K : Type} [Group K] [Finite K] (hK : Open.IsQuasisimple K) {n : ℕ}
    (hn : Nat.card (MulAut (K ⧸ Subgroup.center K)) = n) (h27 : ¬ 3 ^ 3 ∣ n) :
    Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 2 ∧
      ∀ B : Subgroup (MulAut K), IsPGroup 3 B → IsMulCommutative B := by
  have : Group.IsPerfect K := ⟨hK.1⟩
  have hle : ∀ B : Subgroup (MulAut K), IsPGroup 3 B → ∃ k : ℕ, Nat.card B = 3 ^ k ∧ k ≤ 2 := by
    intro B hB
    obtain ⟨k, hk, hdvd⟩ := card_dvd_of_isPGroup_mulAut_of_perfect Nat.prime_three hn B hB
    refine ⟨k, hk, ?_⟩
    by_contra h
    exact h27 ((pow_dvd_pow 3 (by omega)).trans hdvd)
  refine ⟨SectionRank.pRank_le (by norm_num) fun E _ hE => ?_, fun B hB => ?_⟩
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hEp : IsPGroup 3 E := fun x => ⟨1, by
      have := hE.2 x x.2
      rw [pow_one]
      exact Subtype.ext this⟩
    obtain ⟨k, hk, hk2⟩ := hle E hEp
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) hk2
  · obtain ⟨k, hk, hk2⟩ := hle B hB
    exact ⟨⟨fun a b => AGLEmbedding.commute_of_card_eq_pow_le_two Nat.prime_three hk hk2 a b⟩⟩

theorem kFactAlphaSmallAut3 :
    KFactAlphaSmallAut3 := by
  intro K _ _ hK _ _ _ he
  rcases he with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · obtain ⟨e'⟩ := CFSG.GH74.KGroups.A6.equiv_of_alt6 ⟨e⟩
    exact smallAut_conclusion hK (CFSG.GH74.KGroups.A6.card_mulAut e') (by norm_num)
  · obtain ⟨e'⟩ := CFSG.GH74.KGroups.A7.equiv_of_alt e
    exact smallAut_conclusion hK (CFSG.GH74.KGroups.A7.card_mulAut e') (by norm_num)
  · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
    have hcard := CFSG.Monster.B.TwoA.Fischer.catalog_M22_full_automorphism_order.1
    refine smallAut_conclusion hK (n := 887040) ?_ (by norm_num)
    rw [← hcard]
    exact Nat.card_congr (MulAut.congr (e.trans b.symm)).toEquiv

end CFSG.LocalAnalysis.RankThreeTheoremC
