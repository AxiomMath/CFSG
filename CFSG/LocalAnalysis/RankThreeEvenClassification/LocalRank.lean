module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.Helpers

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

@[expose] noncomputable def twoLocalRank (prime : ℕ) (G : Type u) [Group G] [Finite G] : ℕ :=
  twoLocalPrimeRank prime G

theorem twoLocalRank_bddAbove (prime : ℕ) (hprime : prime.Prime)
    (G : Type u) [Group G] [Finite G] :
    BddAbove {rank | ∃ subgroup : Subgroup G,
      IsTwoLocal subgroup ∧ pRank prime subgroup = rank} := by
  refine ⟨Nat.card G, ?_⟩
  rintro rank ⟨subgroup, _, heq⟩
  calc
    rank = pRank prime subgroup := heq.symm
    _ ≤ Nat.card subgroup := pRank_le_card prime hprime subgroup
    _ ≤ Nat.card G := Subgroup.card_le_card_group subgroup

theorem pRank_le_twoLocalRank {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (subgroup : Subgroup G)
    (hlocal : IsTwoLocal subgroup) : pRank prime subgroup ≤ twoLocalRank prime G := by
  exact le_csSup (twoLocalRank_bddAbove prime hprime G) ⟨subgroup, hlocal, rfl⟩

theorem twoLocalRank_le_pRank (prime : ℕ) (hprime : prime.Prime)
    (G : Type u) [Group G] [Finite G] :
    twoLocalRank prime G ≤ pRank prime (⊤ : Subgroup G) := by
  apply csSup_le'
  rintro rank ⟨subgroup, _, heq⟩
  rw [← heq]
  exact pRank_mono prime hprime le_top

theorem twoLocalRank_le_evenRank (prime : ℕ) (hprime : prime.Prime)
    (hodd : prime ≠ 2) (G : Type u) [Group G] [Finite G] :
    twoLocalRank prime G ≤ evenRank G := by
  apply csSup_le'
  rintro rank ⟨subgroup, hlocal, heq⟩
  rw [← heq]
  exact pRank_le_evenRank prime hprime hodd subgroup hlocal

theorem twoLocalRank_attained (prime : ℕ) (hprime : prime.Prime)
    (G : Type u) [Group G] [Finite G] (hpositive : 0 < twoLocalRank prime G) :
    ∃ subgroup : Subgroup G,
      IsTwoLocal subgroup ∧ pRank prime subgroup = twoLocalRank prime G := by
  apply Nat.sSup_mem _ (twoLocalRank_bddAbove prime hprime G)
  by_contra hempty
  have hset := Set.not_nonempty_iff_eq_empty.mp hempty
  simp only [twoLocalRank, CFSG.Open.twoLocalPrimeRank, hset, csSup_empty, Nat.bot_eq_zero] at hpositive
  omega

theorem twoLocalRank_eq_zero_of_not_dvd (prime : ℕ) (hprime : prime.Prime)
    (G : Type u) [Group G] [Finite G] (hnotdvd : ¬prime ∣ Nat.card G) :
    twoLocalRank prime G = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply csSup_le'
  rintro rank ⟨subgroup, _, heq⟩
  rw [← heq, pRank_eq_zero_of_not_dvd prime hprime hnotdvd subgroup]

theorem twoLocalRank_positive_prime_dvd (prime : ℕ) (hprime : prime.Prime)
    (G : Type u) [Group G] [Finite G] (hpositive : 0 < twoLocalRank prime G) :
    prime ∣ Nat.card G := by
  by_contra hnotdvd
  have hzero := twoLocalRank_eq_zero_of_not_dvd prime hprime G hnotdvd
  omega

theorem evenRank_eq_sup_twoLocalRanks (G : Type u) [Group G] [Finite G] :
    evenRank G = sSup {rank | ∃ prime : ℕ,
      prime.Prime ∧ prime ≠ 2 ∧ twoLocalRank prime G = rank} := by
  apply le_antisymm
  · by_cases hpositive : 0 < evenRank G
    · obtain ⟨prime, subgroup, hprime, hodd, hlocal, heq⟩ := evenRank_attained G hpositive
      have hlocalrank : twoLocalRank prime G = evenRank G := by
        apply le_antisymm (twoLocalRank_le_evenRank prime hprime hodd G)
        rw [← heq]
        exact pRank_le_twoLocalRank prime hprime subgroup hlocal
      have hbounded : BddAbove {rank | ∃ otherprime : ℕ,
          otherprime.Prime ∧ otherprime ≠ 2 ∧ twoLocalRank otherprime G = rank} := by
        refine ⟨evenRank G, ?_⟩
        rintro rank ⟨otherprime, hotherprime, hotherodd, hrank⟩
        rw [← hrank]
        exact twoLocalRank_le_evenRank otherprime hotherprime hotherodd G
      exact le_csSup hbounded ⟨prime, hprime, hodd, hlocalrank⟩
    · have hzero : evenRank G = 0 := by omega
      rw [hzero]
      exact Nat.zero_le _
  · apply csSup_le'
    rintro rank ⟨prime, hprime, hodd, heq⟩
    rw [← heq]
    exact twoLocalRank_le_evenRank prime hprime hodd G

theorem local_rank_three_prime_cases (G : Type u) [Group G] [Finite G]
    (hrank : evenRank G = 3) :
    (∃ prime : ℕ, prime.Prime ∧ 3 < prime ∧ twoLocalRank prime G = 3) ∨
    ((∀ prime : ℕ, prime.Prime → 3 < prime → twoLocalRank prime G < 3) ∧
      twoLocalRank 3 G = 3) := by
  rcases rank_three_prime_cases G hrank with hlarge | ⟨hsmall, subgroup, hlocal, heq⟩
  · obtain ⟨prime, subgroup, hprime, hgreater, hlocal, heq⟩ := hlarge
    left
    refine ⟨prime, hprime, hgreater, ?_⟩
    apply le_antisymm
    · have hodd : prime ≠ 2 := by omega
      simpa only [hrank] using twoLocalRank_le_evenRank prime hprime hodd G
    · rw [← heq]
      exact pRank_le_twoLocalRank prime hprime subgroup hlocal
  · right
    constructor
    · intro prime hprime hgreater
      have hbound : twoLocalRank prime G ≤ 2 := by
        apply csSup_le'
        rintro rank ⟨other, hother, hrankeq⟩
        have hlt := hsmall prime other hprime hgreater hother
        omega
      omega
    · apply le_antisymm
      · simpa only [hrank] using twoLocalRank_le_evenRank 3 Nat.prime_three (by omega) G
      · calc
          3 = pRank 3 subgroup := heq.symm
          _ ≤ twoLocalRank 3 G :=
            pRank_le_twoLocalRank 3 Nat.prime_three subgroup hlocal

end CFSG.RankThreeEvenClassification.Helpers
