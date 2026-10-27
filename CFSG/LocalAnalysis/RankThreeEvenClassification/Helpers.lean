module

public import CFSG.Mathlib.GroupTheory.Basic
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.LocalVocabulary

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem exponent_le_prime_power (prime : ℕ) (hprime : prime.Prime) (exponent : ℕ) :
    exponent ≤ prime ^ exponent := by
  have hpower := Nat.mul_le_pow hprime.ne_one exponent
  have htwo := hprime.two_le
  nlinarith

theorem pRank_le_card {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (subgroup : Subgroup G) :
    pRank prime subgroup ≤ Nat.card subgroup := by
  apply csSup_le'
  rintro exponent ⟨elementary, hle, _, hcard⟩
  calc
    exponent ≤ prime ^ exponent := exponent_le_prime_power prime hprime exponent
    _ = Nat.card elementary := hcard.symm
    _ ≤ Nat.card subgroup := Subgroup.card_le_of_le hle

theorem pRank_bddAbove {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (subgroup : Subgroup G) :
    BddAbove {exponent | ∃ elementary : Subgroup G,
      elementary ≤ subgroup ∧ IsElemAbelian prime elementary ∧
        Nat.card elementary = prime ^ exponent} := by
  refine ⟨Nat.card subgroup, ?_⟩
  rintro exponent ⟨elementary, hle, _, hcard⟩
  calc
    exponent ≤ prime ^ exponent := exponent_le_prime_power prime hprime exponent
    _ = Nat.card elementary := hcard.symm
    _ ≤ Nat.card subgroup := Subgroup.card_le_of_le hle

theorem pRank_mono {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) {smaller larger : Subgroup G}
    (hle : smaller ≤ larger) : pRank prime smaller ≤ pRank prime larger :=
  CFSG.SectionRank.pRank_mono hprime.one_lt hle

theorem pRank_attained {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (subgroup : Subgroup G) :
    ∃ elementary : Subgroup G, elementary ≤ subgroup ∧ IsElemAbelian prime elementary ∧
      Nat.card elementary = prime ^ pRank prime subgroup :=
  CFSG.SectionRank.exists_pRank hprime.one_lt subgroup

theorem evenRank_bddAbove (G : Type u) [Group G] [Finite G] :
    BddAbove {rank | ∃ (prime : ℕ) (subgroup : Subgroup G),
      prime.Prime ∧ prime ≠ 2 ∧ IsTwoLocal subgroup ∧ pRank prime subgroup = rank} := by
  refine ⟨Nat.card G, ?_⟩
  rintro rank ⟨prime, subgroup, hprime, _, _, hrank⟩
  calc
    rank = pRank prime subgroup := hrank.symm
    _ ≤ Nat.card subgroup := pRank_le_card prime hprime subgroup
    _ ≤ Nat.card G := Subgroup.card_le_card_group subgroup

theorem pRank_le_evenRank {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (subgroup : Subgroup G) (hlocal : IsTwoLocal subgroup) :
    pRank prime subgroup ≤ evenRank G := by
  exact le_csSup (evenRank_bddAbove G) ⟨prime, subgroup, hprime, hodd, hlocal, rfl⟩

theorem evenRank_attained (G : Type u) [Group G] [Finite G]
    (hpositive : 0 < evenRank G) :
    ∃ (prime : ℕ) (subgroup : Subgroup G), prime.Prime ∧ prime ≠ 2 ∧
      IsTwoLocal subgroup ∧ pRank prime subgroup = evenRank G := by
  apply Nat.sSup_mem _ (evenRank_bddAbove G)
  by_contra hempty
  have hset := Set.not_nonempty_iff_eq_empty.mp hempty
  simp only [evenRank, hset, csSup_empty, Nat.bot_eq_zero] at hpositive
  omega

theorem prime_power_pRank_dvd_card {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (subgroup : Subgroup G) :
    prime ^ pRank prime subgroup ∣ Nat.card subgroup := by
  obtain ⟨elementary, hle, _, hcard⟩ := pRank_attained prime hprime subgroup
  rw [← hcard]
  exact Subgroup.card_dvd_of_le hle

theorem pRank_eq_zero_of_not_dvd {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hnotdvd : ¬prime ∣ Nat.card G)
    (subgroup : Subgroup G) : pRank prime subgroup = 0 := by
  by_contra hnonzero
  have hdiv : prime ∣ prime ^ pRank prime subgroup := by
    obtain ⟨exponent, heq⟩ := Nat.exists_eq_succ_of_ne_zero hnonzero
    rw [heq, pow_succ]
    exact dvd_mul_left prime (prime ^ exponent)
  exact hnotdvd (hdiv.trans ((prime_power_pRank_dvd_card prime hprime subgroup).trans
    (Subgroup.card_subgroup_dvd_card subgroup)))

theorem pRank_le_log_card {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (subgroup : Subgroup G) :
    pRank prime subgroup ≤ Nat.log prime (Nat.card subgroup) := by
  obtain ⟨elementary, hle, _, hcard⟩ := pRank_attained prime hprime subgroup
  apply Nat.le_log_of_pow_le hprime.one_lt
  rw [← hcard]
  exact Subgroup.card_le_of_le hle

theorem evenRank_attained_prime_dvd (G : Type u) [Group G] [Finite G]
    (hpositive : 0 < evenRank G) :
    ∃ (prime : ℕ) (subgroup : Subgroup G), prime.Prime ∧ prime ≠ 2 ∧
      prime ∣ Nat.card G ∧ IsTwoLocal subgroup ∧ pRank prime subgroup = evenRank G := by
  obtain ⟨prime, subgroup, hprime, hodd, hlocal, heq⟩ := evenRank_attained G hpositive
  refine ⟨prime, subgroup, hprime, hodd, ?_, hlocal, heq⟩
  by_contra hnotdvd
  have hzero := pRank_eq_zero_of_not_dvd prime hprime hnotdvd subgroup
  omega

theorem rank_three_prime_cases (G : Type u) [Group G] [Finite G]
    (hrank : evenRank G = 3) :
    (∃ (prime : ℕ) (subgroup : Subgroup G), prime.Prime ∧ 3 < prime ∧
      IsTwoLocal subgroup ∧ pRank prime subgroup = 3) ∨
    ((∀ (prime : ℕ) (subgroup : Subgroup G), prime.Prime → 3 < prime →
      IsTwoLocal subgroup → pRank prime subgroup < 3) ∧
      ∃ subgroup : Subgroup G, IsTwoLocal subgroup ∧ pRank 3 subgroup = 3) := by
  classical
  by_cases hlarge : ∃ (prime : ℕ) (subgroup : Subgroup G), prime.Prime ∧ 3 < prime ∧
      IsTwoLocal subgroup ∧ pRank prime subgroup = 3
  · exact Or.inl hlarge
  · right
    constructor
    · intro prime subgroup hprime hlargeprime hlocal
      have hodd : prime ≠ 2 := by omega
      have hbound := pRank_le_evenRank prime hprime hodd subgroup hlocal
      rw [hrank] at hbound
      have hne : pRank prime subgroup ≠ 3 := by
        intro heq
        exact hlarge ⟨prime, subgroup, hprime, hlargeprime, hlocal, heq⟩
      omega
    · have hpositive : 0 < evenRank G := by omega
      obtain ⟨prime, subgroup, hprime, hodd, hlocal, heq⟩ :=
        evenRank_attained G hpositive
      have hnotlarge : ¬3 < prime := by
        intro hlargeprime
        exact hlarge ⟨prime, subgroup, hprime, hlargeprime, hlocal, heq.trans hrank⟩
      have htwo := hprime.two_le
      have heqprime : prime = 3 := by omega
      subst prime
      exact ⟨subgroup, hlocal, heq.trans hrank⟩

theorem not_isPGroup_of_nonabelian_simple (G : Type u) [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ first second : G, first * second ≠ second * first)
    (prime : ℕ) (hprime : prime.Prime) : ¬IsPGroup prime G := by
  intro hpgroup
  have : Fact prime.Prime := ⟨hprime⟩
  have : Group.IsNilpotent G := hpgroup.isNilpotent
  have : IsCyclic G := inferInstance
  obtain ⟨first, second, hne⟩ := hnonab
  exact hne (mul_comm first second)

theorem twoLocal_ne_top {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ first second : G, first * second ≠ second * first)
    (subgroup : Subgroup G) (hlocal : IsTwoLocal subgroup) : subgroup ≠ ⊤ := by
  obtain ⟨twosubgroup, hnontrivial, hpgroup, heq⟩ := hlocal
  intro htop
  have hnormal : twosubgroup.Normal := Subgroup.normalizer_eq_top_iff.mp (heq.symm.trans htop)
  rcases CFSG.eq_bot_or_eq_top_of_normal twosubgroup hnormal with hbot | hwhole
  · exact hnontrivial hbot
  · subst twosubgroup
    exact not_isPGroup_of_nonabelian_simple G hnonab 2 Nat.prime_two
      (hpgroup.of_equiv Subgroup.topEquiv)

theorem twoLocal_ne_bot {G : Type u} [Group G]
    (subgroup : Subgroup G) (hlocal : IsTwoLocal subgroup) : subgroup ≠ ⊥ := by
  obtain ⟨twosubgroup, hnontrivial, _, heq⟩ := hlocal
  intro hbot
  apply hnontrivial
  apply le_antisymm _ bot_le
  have hle : twosubgroup ≤ Subgroup.normalizer (twosubgroup : Set G) :=
    Subgroup.le_normalizer
  simpa only [← heq, hbot] using hle

theorem rank_three_has_proper_local (G : Type u) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ first second : G, first * second ≠ second * first)
    (hrank : evenRank G = 3) :
    ∃ (prime : ℕ) (subgroup : Subgroup G), prime.Prime ∧ prime ≠ 2 ∧
      prime ∣ Nat.card G ∧ IsTwoLocal subgroup ∧ subgroup ≠ ⊤ ∧
      pRank prime subgroup = 3 := by
  have hpositive : 0 < evenRank G := by omega
  obtain ⟨prime, subgroup, hprime, hodd, hdiv, hlocal, heq⟩ :=
    evenRank_attained_prime_dvd G hpositive
  exact ⟨prime, subgroup, hprime, hodd, hdiv, hlocal,
    twoLocal_ne_top hnonab subgroup hlocal, heq.trans hrank⟩

end CFSG.RankThreeEvenClassification.Helpers
