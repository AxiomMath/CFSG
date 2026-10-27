module

public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIO

open Module Finset QuadraticMap
open CFSG.GroupTheory.WeirSylow (IsPlusType)

theorem exists_odd_prime_dvd_pow_four_add_one {q : ℕ} (hq : Odd q) (h3 : 3 ≤ q) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ∣ q ^ 4 + 1 := by
  obtain ⟨k, rfl⟩ := hq
  set X := 4 * k ^ 4 + 8 * k ^ 3 + 6 * k ^ 2 + 2 * k with hX
  have hk : 1 ≤ k := by omega
  have hX1 : 1 ≤ X := by
    have : 2 * 1 ≤ 2 * k := by omega
    omega
  have hm1 : 2 * X + 1 ≠ 1 := by omega
  have hprime := Nat.minFac_prime hm1
  refine ⟨(2 * X + 1).minFac, hprime, fun h2 => ?_, ?_⟩
  · have h := Nat.minFac_dvd (2 * X + 1)
    rw [h2] at h
    omega
  · exact (Nat.minFac_dvd _).trans ⟨2, by rw [hX]; ring⟩

theorem two_ne_zero_zmod {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) : (2 : ZMod ℓ) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h
  have hdvd := (ZMod.natCast_eq_zero_iff 2 ℓ).1 h'
  exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 hdvd)

theorem pow_facts {R : Type*} [CommRing R] (h2 : (2 : R) ≠ 0) {x : R} (hx : x ^ 4 = -1) :
    x ≠ 0 ∧ (∀ j ∈ Icc 1 3, (x ^ 2) ^ j - 1 ≠ 0) ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ 3 → x ^ j - 1 ≠ 0 ∧ x ^ j + 1 ≠ 0 := by
  have h4 : x ^ 4 ≠ 1 := by
    intro h
    apply h2
    linear_combination hx - h
  have h6 : x ^ 6 ≠ 1 := by
    intro h
    apply h4
    have e : x ^ 2 = -1 := by linear_combination -h + x ^ 2 * hx
    linear_combination (x ^ 2 - 1) * e
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply h2
    linear_combination 2 * hx
  refine ⟨hx0, fun j hj => ?_, fun j hj1 hj3 => ⟨?_, ?_⟩⟩
  · obtain ⟨hj1, hj3⟩ := mem_Icc.mp hj
    intro h
    interval_cases j
    · exact h4 (by linear_combination (x ^ 2 + 1) * h)
    · exact h4 (by linear_combination h)
    · exact h6 (by linear_combination h)
  · intro h
    interval_cases j
    · exact h4 (by linear_combination (x ^ 3 + x ^ 2 + x + 1) * h)
    · exact h4 (by linear_combination (x ^ 2 + 1) * h)
    · exact h6 (by linear_combination (x ^ 3 + 1) * h)
  · intro h
    interval_cases j
    · exact h4 (by linear_combination (x ^ 3 - x ^ 2 + x - 1) * h)
    · exact h4 (by linear_combination (x ^ 2 - 1) * h)
    · exact h6 (by linear_combination (x ^ 3 - 1) * h)

variable {K : Type} [Field K] [Finite K]

omit [Field K] [Finite K] in
theorem prod_ne_zero {R : Type*} [CommRing R] [IsDomain R] (h2 : (2 : R) ≠ 0) {x : R}
    (hx : x ^ 4 = -1) {n : ℕ} (hn : n ≤ 3) : ∏ i ∈ Icc 1 n, ((x ^ 2) ^ i - 1) ≠ 0 := by
  rw [prod_ne_zero_iff]
  intro i hi
  obtain ⟨hi1, hin⟩ := mem_Icc.mp hi
  exact (pow_facts h2 hx).2.1 i (mem_Icc.mpr ⟨hi1, by omega⟩)

theorem not_dvd_card {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hdvd : ℓ ∣ Nat.card K ^ 4 + 1)
    (h2 : ringChar K ≠ 2) {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {Q : QuadraticForm K W} (hQ : (polarBilin Q).Nondegenerate) (h1 : 1 ≤ finrank K W)
    (h7 : finrank K W ≤ 7) : ¬ ℓ ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set x : ZMod ℓ := (Nat.card K : ZMod ℓ) with hxdef
  have hx : x ^ 4 = -1 := by
    have h := (ZMod.natCast_eq_zero_iff _ ℓ).2 hdvd
    push_cast at h
    exact eq_neg_of_add_eq_zero_left h
  have h2ℓ := two_ne_zero_zmod hℓ hℓ2
  obtain ⟨hx0, -, hj⟩ := pow_facts h2ℓ hx
  intro hN
  have hN' := (ZMod.natCast_eq_zero_iff _ ℓ).2 hN
  rcases Nat.even_or_odd (finrank K W) with ⟨n, hn⟩ | ⟨n, hn⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hdim : finrank K W = 2 * (m + 1) := by omega
    by_cases hplus : IsPlusType Q
    · have hc := GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hQ hdim
        (Or.inl ⟨rfl, hplus⟩)
      have hc' := congrArg (Int.cast : ℤ → ZMod ℓ) hc
      push_cast at hc'
      rw [hN', ← hxdef] at hc'
      have hm : m + 1 ≤ 3 := by omega
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2ℓ (pow_ne_zero _ hx0))
        (hj (m + 1) (by omega) hm).1) (prod_ne_zero h2ℓ hx (by omega)) hc'.symm
    · have hc := GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hQ hdim
        (Or.inr ⟨rfl, hplus⟩)
      have hc' := congrArg (Int.cast : ℤ → ZMod ℓ) hc
      push_cast at hc'
      rw [hN', ← hxdef, sub_neg_eq_add] at hc'
      have hm : m + 1 ≤ 3 := by omega
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2ℓ (pow_ne_zero _ hx0))
        (hj (m + 1) (by omega) hm).2) (prod_ne_zero h2ℓ hx (by omega)) hc'.symm
  · have hc := GroupTheory.WeirSylow.natCard_orthogonalGroup_odd h2 hQ (n := n) (by omega)
    have hc' := congrArg (Int.cast : ℤ → ZMod ℓ) hc
    push_cast at hc'
    rw [hN', ← hxdef] at hc'
    exact mul_ne_zero (mul_ne_zero h2ℓ (pow_ne_zero _ hx0)) (prod_ne_zero h2ℓ hx (by omega))
      hc'.symm

end OIO

end CFSG.ComponentClassification.CatFactsL4U4
