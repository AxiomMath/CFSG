module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem smallRank_localRank_le_three (hS : Setting G) {f : ℕ} (hfp : f.Prime) (hf2 : f ≠ 2) :
    rankThreeLocalRank f G ≤ 3 := by
  have h := rankThreeLocalRank_le_evenRank (G := G) f hfp hf2
  rwa [hS.rank] at h

theorem localRank_le_two_of_three (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G}
    (hs : SmallRankSituation G 3 P M) {f : ℕ} (hfp : f.Prime) (h5 : 5 ≤ f) :
    rankThreeLocalRank f G ≤ 2 := by
  classical
  by_contra hlt
  push Not at hlt
  have hf2 : f ≠ 2 := by omega
  have hle := rankThreeLocalRank_le_evenRank (G := G) f hfp hf2
  rw [hS.rank] at hle
  have hf3 : rankThreeLocalRank f G = 3 := by omega
  obtain ⟨H, -, hHr⟩ := rankThreeLocalRank_attained (G := G) f (by omega)
  have hdvd : f ∣ Nat.card G := prime_dvd_card_of_pRank_pos f H (by omega)
  have h3le := rankThreeLocalRank_le_evenRank (G := G) 3 Nat.prime_three (by norm_num)
  rw [hS.rank] at h3le
  have h3 := hs.mem_sigmaA
  dsimp only [rankThreeSigmaA] at h3
  split_ifs at h3 with h₁ h₂ h₃
  · exact absurd h3.2.2.2 (by omega)
  · exact absurd h3.2.1 (by norm_num)
  · exact absurd h3.2.1 (by norm_num)
  · exact h₃ ⟨f, hfp, by omega, hdvd, hf3⟩

theorem smallRankInvolutionRankLE_of_localRank {f r : ℕ} (hfp : f.Prime) (S X : Subgroup G)
    (h : rankThreeLocalRank f G ≤ r) : SmallRankInvolutionRankLE f r S X := by
  intro y _ hy2 hy1
  have hord : orderOf y = 2 := orderOf_eq_prime hy2 hy1
  have hloc : IsTwoLocal (normalizer (zpowers y : Set G)) :=
    ⟨zpowers y, by rwa [Ne, zpowers_eq_bot],
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one]), rfl⟩
  have hle : centralizer ({y} : Set G) ≤ normalizer (zpowers y : Set G) := by
    intro g hg
    have hc : Commute g y := mem_centralizer_singleton_iff.mp hg
    rw [mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hw
      rw [(hc.zpow_right j).eq, mul_inv_cancel_right]
      exact zpow_mem_zpowers y j
    · intro hw
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hw
      have hc' : Commute g⁻¹ (y ^ j) := (hc.zpow_right j).inv_left
      have h1 : w = g⁻¹ * (g * w * g⁻¹) * g := by group
      rw [← hj, hc'.eq, inv_mul_cancel_right] at h1
      rw [h1]
      exact zpow_mem_zpowers y j
  calc CFSG.Open.pRank f (X ⊓ centralizer ({y} : Set G))
      ≤ CFSG.Open.pRank f (centralizer ({y} : Set G)) :=
        pRank_mono f hfp.one_lt inf_le_right
    _ ≤ CFSG.Open.pRank f (normalizer (zpowers y : Set G)) := pRank_mono f hfp.one_lt hle
    _ ≤ rankThreeLocalRank f G := local_pRank_le_localRank f hfp.one_lt _ hloc
    _ ≤ r := h

end CFSG.LocalAnalysis.RankThreeTheoremC
