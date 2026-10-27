module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem sigmaA_eq_three (hrank : evenRank G = 3) (h : 3 ∈ rankThreeSigmaA G) :
    rankThreeSigmaA G = {3} := by
  classical
  dsimp only [rankThreeSigmaA] at h ⊢
  split_ifs at h ⊢ with h1 h2 h3
  · exfalso
    have hlt := h.2.2.2
    have hle := rankThreeLocalRank_le_evenRank (G := G) 3 Nat.prime_three (by norm_num)
    omega
  · exact absurd h.2.1 (by norm_num)
  · exact absurd h.2.1 (lt_irrefl 3)
  · ext p
    simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hp, hodd, hdvd, hloc⟩
      by_contra hne
      exact h3 ⟨p, hp, by have := hp.two_le; omega, hdvd, hloc⟩
    · rintro rfl
      exact h

theorem sigmaA_eq_five (hrank : evenRank G = 3) (h : 5 ∈ rankThreeSigmaA G) :
    rankThreeSigmaA G = {5} := by
  classical
  dsimp only [rankThreeSigmaA] at h ⊢
  split_ifs at h ⊢ with h1 h2 h3
  · exfalso
    have hlt := h.2.2.2
    have hle := rankThreeLocalRank_le_evenRank (G := G) 5 Nat.prime_five (by norm_num)
    omega
  · exact absurd h.2.1 (lt_irrefl 5)
  · ext p
    simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hp, hgt3, hdvd, hloc⟩
      by_cases hgt5 : 5 < p
      · exfalso
        exact h2 ⟨p, hp, hgt5, hdvd, hloc⟩
      · have hne4 : p ≠ 4 := by
          rintro rfl
          norm_num at hp
        omega
    · rintro rfl
      exact h
  · exfalso
    exact h3 ⟨5, h.1, by norm_num, h.2.2.1, h.2.2.2⟩

theorem seven_le_of_mem_sigmaA (hrank : evenRank G = 3) {q : ℕ} (hq : q ∈ rankThreeSigmaA G)
    (h3 : q ≠ 3) (h5 : q ≠ 5) : 7 ≤ q := by
  have hprime : q.Prime := sigmaA_prime q hq
  have hodd : q ≠ 2 := sigmaA_odd q hq
  have h2 : 2 ≤ q := hprime.two_le
  have h4 : q ≠ 4 := by
    rintro rfl
    norm_num at hprime
  have h6 : q ≠ 6 := by
    rintro rfl
    norm_num at hprime
  omega

theorem seven_le_of_mem_sigmaA_of_seven_le (hrank : evenRank G = 3) {q : ℕ}
    (hq : q ∈ rankThreeSigmaA G) (h7 : 7 ≤ q) : ∀ r ∈ rankThreeSigmaA G, 7 ≤ r := by
  intro r hr
  have hr3 : r ≠ 3 := by
    rintro rfl
    rw [sigmaA_eq_three hrank hr, Set.mem_singleton_iff] at hq
    omega
  have hr5 : r ≠ 5 := by
    rintro rfl
    rw [sigmaA_eq_five hrank hr, Set.mem_singleton_iff] at hq
    omega
  exact seven_le_of_mem_sigmaA hrank hr hr3 hr5

end CFSG.LocalAnalysis.RankThreeUC.S15
