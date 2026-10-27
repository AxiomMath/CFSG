module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxSpor

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace KxCfg

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G} {T S L : Subgroup G}

theorem le_of_section_three_spor (hL613 : L613) (h2401 : KFact2401Spor)
    (c : KxCfg p P M x z T S L) {s : TauCeti.SporadicName}
    (e : Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic s).Group)) (h3 : 2 ≤ CFSG.Open.pRank 3 L)
    (hs : s ≠ .M11) {H N : Subgroup G} (hHL : H ≤ L) (hHM : H ≤ M)
    (hsec : S622IsSimpleSection H N) (hzH : z ∈ H) (hzN : z ∉ N) (h3d : 3 ∣ N.relIndex H) :
    False := by
  have hp5 : 5 ≤ p := c.conf.config.situation.p_ge
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsE : GLBStronglyEmbedded 3 M :=
    c.stronglyEmbedded hL613 hHL hHM hsec hzH hzN Nat.prime_three (by norm_num) (by omega) h3d
  have h3H : 3 ∣ Nat.card H := h3d.trans (Subgroup.index_dvd_card (N.subgroupOf H))
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 3 h3H
  have ht3 : IsPGroup 3 (zpowers (t : G)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ht, pow_one]
  obtain ⟨E₃, hE₃syl, hXE₃⟩ := exists_isSylowOf_ge (f := 3) (zpowers_le.mpr (hHL t.2)) ht3
  have ht1 : (t : G) ≠ 1 := by
    intro h1
    have : t = 1 := Subtype.ext h1
    rw [this, orderOf_one] at ht
    omega
  have hE₃M : E₃ ⊓ M ≠ ⊥ := by
    intro hbot
    have hmem : (t : G) ∈ E₃ ⊓ M := ⟨hXE₃ (mem_zpowers _), hHM t.2⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact ht1 hmem
  have hE₃p : IsPGroup 3 E₃ := hE₃syl.isPGroup
  rcases h2401 G L s e h3 with h | h
  · have hLJ : L ≤ M ⊓ L := h E₃ hE₃syl (M ⊓ L) fun S₀ hS₀E hS₀1 =>
      inf_le_inf_right L (normalizer_le_of_stronglyEmbedded_sub hsE hE₃p hE₃M hS₀E hS₀1)
    exact c.not_le (hLJ.trans inf_le_left)
  · exact absurd h hs

end KxCfg

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
