module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalRank

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

def aschbacherStratumOne (G : Type u) [Group G] [Finite G] : Set ℕ :=
  {prime | prime.Prime ∧ prime ≠ 2 ∧ prime ∣ Nat.card G ∧ 3 < twoLocalRank prime G}

def aschbacherStratumTwo (G : Type u) [Group G] [Finite G] : Set ℕ :=
  {prime | prime.Prime ∧ 5 < prime ∧ prime ∣ Nat.card G ∧ twoLocalRank prime G = 3}

def aschbacherStratumThree (G : Type u) [Group G] [Finite G] : Set ℕ :=
  {prime | prime.Prime ∧ 3 < prime ∧ prime ∣ Nat.card G ∧ twoLocalRank prime G = 3}

def aschbacherStratumFour (G : Type u) [Group G] [Finite G] : Set ℕ :=
  {prime | prime.Prime ∧ prime ≠ 2 ∧ prime ∣ Nat.card G ∧ twoLocalRank prime G = 3}

@[expose] noncomputable def aschbacherPrimes (G : Type u) [Group G] [Finite G] : Set ℕ := by
  classical
  exact if (aschbacherStratumOne G).Nonempty then aschbacherStratumOne G
    else if (aschbacherStratumTwo G).Nonempty then aschbacherStratumTwo G
    else if (aschbacherStratumThree G).Nonempty then aschbacherStratumThree G
    else if (aschbacherStratumFour G).Nonempty then aschbacherStratumFour G else ∅

theorem prime_divisors_finite (G : Type u) [Group G] [Finite G] :
    {prime : ℕ | prime.Prime ∧ prime ∣ Nat.card G}.Finite := by
  apply (Set.finite_Iic (Nat.card G)).subset
  rintro prime ⟨_, hdiv⟩
  exact Nat.le_of_dvd Nat.card_pos hdiv

theorem aschbacher_strata_finite (G : Type u) [Group G] [Finite G] :
    (aschbacherStratumOne G).Finite ∧ (aschbacherStratumTwo G).Finite ∧
      (aschbacherStratumThree G).Finite ∧ (aschbacherStratumFour G).Finite := by
  have hfinite := prime_divisors_finite G
  refine ⟨hfinite.subset ?_, hfinite.subset ?_, hfinite.subset ?_, hfinite.subset ?_⟩
  all_goals
    rintro prime ⟨hprime, _, hdiv, _⟩
    exact ⟨hprime, hdiv⟩

theorem aschbacherPrimes_finite (G : Type u) [Group G] [Finite G] :
    (aschbacherPrimes G).Finite := by
  classical
  obtain ⟨hfirst, hsecond, hthird, hfourth⟩ := aschbacher_strata_finite G
  unfold aschbacherPrimes
  split_ifs <;> first | assumption | exact Set.finite_empty

theorem aschbacherStratumOne_eq_empty (G : Type u) [Group G] [Finite G]
    (hrank : evenRank G = 3) : aschbacherStratumOne G = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro prime ⟨hprime, hodd, _, hgreater⟩
  have hbound := twoLocalRank_le_evenRank prime hprime hodd G
  omega

theorem aschbacherStratumFour_nonempty (G : Type u) [Group G] [Finite G]
    (hrank : evenRank G = 3) : (aschbacherStratumFour G).Nonempty := by
  have hpositive : 0 < evenRank G := by omega
  obtain ⟨prime, subgroup, hprime, hodd, hdiv, hlocal, heq⟩ :=
    evenRank_attained_prime_dvd G hpositive
  refine ⟨prime, hprime, hodd, hdiv, ?_⟩
  apply le_antisymm
  · simpa only [hrank] using twoLocalRank_le_evenRank prime hprime hodd G
  · calc
      3 = pRank prime subgroup := (heq.trans hrank).symm
      _ ≤ twoLocalRank prime G := pRank_le_twoLocalRank prime hprime subgroup hlocal

theorem aschbacherStratumTwo_mem_iff (G : Type u) [Group G] [Finite G] (prime : ℕ) :
    prime ∈ aschbacherStratumTwo G ↔
      prime.Prime ∧ 5 < prime ∧ twoLocalRank prime G = 3 := by
  constructor
  · rintro ⟨hprime, hgreater, _, heq⟩
    exact ⟨hprime, hgreater, heq⟩
  · rintro ⟨hprime, hgreater, heq⟩
    have hpositive : 0 < twoLocalRank prime G := by omega
    exact ⟨hprime, hgreater, twoLocalRank_positive_prime_dvd prime hprime G hpositive, heq⟩

theorem aschbacherStratumThree_subset_five (G : Type u) [Group G] [Finite G]
    (hsecond : aschbacherStratumTwo G = ∅) : aschbacherStratumThree G ⊆ {5} := by
  rintro prime ⟨hprime, hgreater, hdiv, heq⟩
  have hle : prime ≤ 5 := by
    by_contra hnotle
    have hmem : prime ∈ aschbacherStratumTwo G := ⟨hprime, by omega, hdiv, heq⟩
    rw [hsecond] at hmem
    exact hmem
  have hparity := hprime.eq_two_or_odd
  have heqprime : prime = 5 := by omega
  exact Set.mem_singleton_iff.mpr heqprime

theorem aschbacherStratumThree_eq_five (G : Type u) [Group G] [Finite G]
    (hsecond : aschbacherStratumTwo G = ∅) (hfive : twoLocalRank 5 G = 3) :
    aschbacherStratumThree G = {5} := by
  apply Set.Subset.antisymm (aschbacherStratumThree_subset_five G hsecond)
  intro prime hmem
  have heqprime := Set.mem_singleton_iff.mp hmem
  subst prime
  have hpositive : 0 < twoLocalRank 5 G := by omega
  exact ⟨Nat.prime_five, by omega,
    twoLocalRank_positive_prime_dvd 5 Nat.prime_five G hpositive, hfive⟩

theorem aschbacherStratumThree_eq_empty (G : Type u) [Group G] [Finite G]
    (hsecond : aschbacherStratumTwo G = ∅) (hfive : twoLocalRank 5 G < 3) :
    aschbacherStratumThree G = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro prime hmem
  have heqprime := Set.mem_singleton_iff.mp
    (aschbacherStratumThree_subset_five G hsecond hmem)
  have heq := hmem.2.2.2
  subst prime
  omega

theorem aschbacherStratumFour_eq_three (G : Type u) [Group G] [Finite G]
    (hrank : evenRank G = 3) (hsecond : aschbacherStratumTwo G = ∅)
    (hfive : twoLocalRank 5 G < 3) : aschbacherStratumFour G = {3} := by
  have hthird := aschbacherStratumThree_eq_empty G hsecond hfive
  have hsubset : aschbacherStratumFour G ⊆ {3} := by
    rintro prime ⟨hprime, hodd, hdiv, heq⟩
    have hle : prime ≤ 3 := by
      by_contra hnotle
      have hmem : prime ∈ aschbacherStratumThree G := ⟨hprime, by omega, hdiv, heq⟩
      rw [hthird] at hmem
      exact hmem
    have htwo := hprime.two_le
    have heqprime : prime = 3 := by omega
    exact Set.mem_singleton_iff.mpr heqprime
  apply Set.Subset.antisymm hsubset
  obtain ⟨prime, hmem⟩ := aschbacherStratumFour_nonempty G hrank
  have heqprime := Set.mem_singleton_iff.mp (hsubset hmem)
  subst prime
  intro other hother
  have heqother := Set.mem_singleton_iff.mp hother
  subst other
  exact hmem

theorem aschbacherPrimes_eq_second (G : Type u) [Group G] [Finite G]
    (hrank : evenRank G = 3) (hsecond : (aschbacherStratumTwo G).Nonempty) :
    aschbacherPrimes G = aschbacherStratumTwo G := by
  classical
  simp only [aschbacherPrimes, aschbacherStratumOne_eq_empty G hrank,
    Set.not_nonempty_empty, ite_false, hsecond, ite_true]

theorem aschbacherPrimes_eq_five (G : Type u) [Group G] [Finite G]
    (hrank : evenRank G = 3) (hsecond : aschbacherStratumTwo G = ∅)
    (hfive : twoLocalRank 5 G = 3) : aschbacherPrimes G = {5} := by
  classical
  have hthird := aschbacherStratumThree_eq_five G hsecond hfive
  simp only [aschbacherPrimes, aschbacherStratumOne_eq_empty G hrank, hsecond,
    Set.not_nonempty_empty, ite_false, hthird, Set.singleton_nonempty, ite_true]

theorem aschbacherPrimes_eq_three (G : Type u) [Group G] [Finite G]
    (hrank : evenRank G = 3) (hsecond : aschbacherStratumTwo G = ∅)
    (hfive : twoLocalRank 5 G < 3) : aschbacherPrimes G = {3} := by
  classical
  have hthird := aschbacherStratumThree_eq_empty G hsecond hfive
  have hfourth := aschbacherStratumFour_eq_three G hrank hsecond hfive
  simp only [aschbacherPrimes, aschbacherStratumOne_eq_empty G hrank, hsecond, hthird,
    Set.not_nonempty_empty, ite_false, hfourth, Set.singleton_nonempty, ite_true]

theorem aschbacherPrimes_cases (G : Type u) [Group G] [Finite G]
    (hrank : evenRank G = 3) :
    ((aschbacherStratumTwo G).Nonempty ∧
      aschbacherPrimes G = aschbacherStratumTwo G) ∨
    (aschbacherStratumTwo G = ∅ ∧ twoLocalRank 5 G = 3 ∧ aschbacherPrimes G = {5}) ∨
    (aschbacherStratumTwo G = ∅ ∧ twoLocalRank 5 G < 3 ∧
      aschbacherPrimes G = {3} ∧ twoLocalRank 3 G = 3) := by
  classical
  by_cases hsecond : (aschbacherStratumTwo G).Nonempty
  · exact Or.inl ⟨hsecond, aschbacherPrimes_eq_second G hrank hsecond⟩
  · have hempty := Set.not_nonempty_iff_eq_empty.mp hsecond
    by_cases hfive : twoLocalRank 5 G = 3
    · exact Or.inr (Or.inl ⟨hempty, hfive, aschbacherPrimes_eq_five G hrank hempty hfive⟩)
    · have hbound := twoLocalRank_le_evenRank 5 Nat.prime_five (by omega) G
      have hless : twoLocalRank 5 G < 3 := by omega
      have hfourth := aschbacherStratumFour_eq_three G hrank hempty hless
      have hmem : 3 ∈ aschbacherStratumFour G := by
        rw [hfourth]
        exact Set.mem_singleton 3
      exact Or.inr (Or.inr ⟨hempty, hless,
        aschbacherPrimes_eq_three G hrank hempty hless, hmem.2.2.2⟩)

theorem aschbacherPrimes_nonempty (G : Type u) [Group G] [Finite G]
    (hrank : evenRank G = 3) : (aschbacherPrimes G).Nonempty := by
  rcases aschbacherPrimes_cases G hrank with ⟨hsecond, heq⟩ |
      ⟨_, _, heq⟩ | ⟨_, _, heq, _⟩
  · exact heq.symm ▸ hsecond
  · rw [heq]
    exact Set.singleton_nonempty 5
  · rw [heq]
    exact Set.singleton_nonempty 3

theorem aschbacherPrimes_mem_rank_three (G : Type u) [Group G] [Finite G]
    (hrank : evenRank G = 3) (prime : ℕ) (hmem : prime ∈ aschbacherPrimes G) :
    prime.Prime ∧ prime ≠ 2 ∧ prime ∣ Nat.card G ∧ twoLocalRank prime G = 3 := by
  rcases aschbacherPrimes_cases G hrank with ⟨_, heq⟩ |
      ⟨_, hfive, heq⟩ | ⟨_, _, heq, hthree⟩
  · rw [heq] at hmem
    obtain ⟨hprime, hgreater, hdiv, hlocalrank⟩ := hmem
    exact ⟨hprime, by omega, hdiv, hlocalrank⟩
  · rw [heq, Set.mem_singleton_iff] at hmem
    subst prime
    have hpositive : 0 < twoLocalRank 5 G := by omega
    exact ⟨Nat.prime_five, by omega,
      twoLocalRank_positive_prime_dvd 5 Nat.prime_five G hpositive, hfive⟩
  · rw [heq, Set.mem_singleton_iff] at hmem
    subst prime
    have hpositive : 0 < twoLocalRank 3 G := by omega
    exact ⟨Nat.prime_three, by omega,
      twoLocalRank_positive_prime_dvd 3 Nat.prime_three G hpositive, hthree⟩

theorem aschbacherPrimes_eq_three_iff (G : Type u) [Group G] [Finite G]
    (hrank : evenRank G = 3) :
    aschbacherPrimes G = {3} ↔
      ∀ prime : ℕ, prime.Prime → 3 < prime → twoLocalRank prime G < 3 := by
  constructor
  · intro hthree prime hprime hgreater
    rcases aschbacherPrimes_cases G hrank with ⟨hsecond, heq⟩ |
        ⟨_, _, heq⟩ | ⟨hsecond, hfive, _, _⟩
    · obtain ⟨otherprime, hmem⟩ := hsecond
      have hselected : otherprime ∈ aschbacherPrimes G := heq.symm ▸ hmem
      rw [hthree, Set.mem_singleton_iff] at hselected
      have hothergreater := hmem.2.1
      omega
    · have hselected : 5 ∈ aschbacherPrimes G := by
        rw [heq]
        exact Set.mem_singleton 5
      rw [hthree, Set.mem_singleton_iff] at hselected
      omega
    · have hodd : prime ≠ 2 := by omega
      have hbound := twoLocalRank_le_evenRank prime hprime hodd G
      have hne : twoLocalRank prime G ≠ 3 := by
        intro heqrank
        have hpositive : 0 < twoLocalRank prime G := by omega
        have hdiv := twoLocalRank_positive_prime_dvd prime hprime G hpositive
        have hthirdmem : prime ∈ aschbacherStratumThree G :=
          ⟨hprime, hgreater, hdiv, heqrank⟩
        have hthird := aschbacherStratumThree_eq_empty G hsecond hfive
        rw [hthird] at hthirdmem
        exact hthirdmem
      omega
  · intro hsmall
    have hsecond : aschbacherStratumTwo G = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro prime ⟨hprime, hgreater, _, heq⟩
      have hless := hsmall prime hprime (by omega)
      omega
    exact aschbacherPrimes_eq_three G hrank hsecond (hsmall 5 Nat.prime_five (by omega))

theorem aschbacherPrimes_ne_three_iff (G : Type u) [Group G] [Finite G]
    (hrank : evenRank G = 3) :
    aschbacherPrimes G ≠ {3} ↔
      ∃ prime : ℕ, prime.Prime ∧ 3 < prime ∧ twoLocalRank prime G = 3 := by
  constructor
  · intro hne
    rcases local_rank_three_prime_cases G hrank with hlarge | ⟨hsmall, _⟩
    · exact hlarge
    · exact False.elim (hne ((aschbacherPrimes_eq_three_iff G hrank).mpr hsmall))
  · rintro ⟨prime, hprime, hgreater, heq⟩ hthree
    have hless := (aschbacherPrimes_eq_three_iff G hrank).mp hthree prime hprime hgreater
    omega

end CFSG.RankThreeEvenClassification.Helpers
