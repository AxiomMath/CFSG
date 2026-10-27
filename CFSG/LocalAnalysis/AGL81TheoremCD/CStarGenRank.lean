module

public import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGen
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem three_le_localRank_of_mem_sigmaA {p : ℕ}
    (hp : p ∈ CFSG.Open.rankThreeSigmaA G) :
    3 ≤ CFSG.Open.rankThreeLocalRank p G := by
  classical
  dsimp only [CFSG.Open.rankThreeSigmaA] at hp
  split_ifs at hp <;> simp only [Set.mem_setOf_eq] at hp <;> omega

theorem mem_sigmaA_of_four_le_localRank {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : 4 ≤ CFSG.Open.rankThreeLocalRank p G) :
    p ∈ CFSG.Open.rankThreeSigmaA G := by
  classical
  obtain ⟨localGroup, -, hrank⟩ :=
    rankThreeLocalRank_attained p (lt_of_lt_of_le (by norm_num) h)
  have hpos : 0 < CFSG.Open.pRank p localGroup := by
    rw [hrank]
    exact lt_of_lt_of_le (by norm_num) h
  have hdvd : p ∣ Nat.card G := prime_dvd_card_of_pRank_pos p localGroup hpos
  have hS1 : p ∈ {p : ℕ | p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G ∧
      3 < CFSG.Open.rankThreeLocalRank p G} :=
    ⟨hp, hp2, hdvd, lt_of_lt_of_le (by norm_num) h⟩
  have hne : ({p : ℕ | p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G ∧
      3 < CFSG.Open.rankThreeLocalRank p G} : Set ℕ).Nonempty := ⟨p, hS1⟩
  dsimp only [CFSG.Open.rankThreeSigmaA]
  rw [if_pos hne]
  exact hS1

theorem three_le_pRank_top_of_mem_sigmaA {p : ℕ}
    (hp : p ∈ CFSG.Open.rankThreeSigmaA G) :
    3 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  have hlocal := three_le_localRank_of_mem_sigmaA hp
  obtain ⟨localGroup, -, hrank⟩ :=
    rankThreeLocalRank_attained p (lt_of_lt_of_le (by norm_num) hlocal)
  have hmono := pRank_mono p (sigmaA_prime p hp).one_lt
    (show localGroup ≤ (⊤ : Subgroup G) from le_top)
  calc
    3 ≤ CFSG.Open.rankThreeLocalRank p G := hlocal
    _ = CFSG.Open.pRank p localGroup := hrank.symm
    _ ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := hmono

theorem CStarGen.three_le_pRank_of_mem_sigmaSet (hC : CStarGen G) {N : Subgroup G}
    (hN : CFSG.Open.rankThreeIsMaxTwoLocal N) {q : ℕ} (hq : q ∈ sigmaSet G N) :
    3 ≤ CFSG.Open.pRank q N := by
  obtain ⟨P, hPN, -⟩ := hC.almost N hN q hq
  have hqA : q ∈ CFSG.Open.rankThreeSigmaA G := hq.1
  have hqprime : q.Prime := sigmaA_prime q hqA
  obtain ⟨Q, hQ⟩ := exists_sylow_rank_at_least_three q hqprime
    (three_le_pRank_top_of_mem_sigmaA hqA)
  have hP : 3 ≤ CFSG.Open.pRank q (P : Subgroup G) := by
    rw [← sylow_pRank_eq q hqprime Q P]
    exact hQ
  exact hP.trans (pRank_mono q hqprime.one_lt hPN)

theorem CStarGen.pRank_le_three_of_isTwoLocal (hC : CStarGen G) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hrσ : r ∉ CFSG.Open.rankThreeSigmaA G) {H : Subgroup G}
    (hH : CFSG.Open.IsTwoLocal H) : CFSG.Open.pRank r H ≤ 3 :=
  (local_pRank_le_localRank r hr.one_lt H hH).trans (hC.off_sigma r hr hr2 hrσ).1

theorem CStarGen.pRank_le_three_of_not_mem_sigmaSet (hC : CStarGen G) {N : Subgroup G}
    (hN : CFSG.Open.rankThreeIsMaxTwoLocal N) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrN : r ∉ sigmaSet G N) : CFSG.Open.pRank r N ≤ 3 := by
  by_cases hrA : r ∈ CFSG.Open.rankThreeSigmaA G
  · have hnot : ¬ 2 ≤ CFSG.Open.pRank r N := fun h2 => hrN ⟨hrA, h2⟩
    omega
  · exact hC.pRank_le_three_of_isTwoLocal hr hr2 hrA hN.1

end CFSG.LocalAnalysis.AGL81TheoremCD
