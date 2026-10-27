module

public import CFSG.LinearAlgebra.SL2MinimalFaithfulZsigmondy
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51e

@[expose] def IsPrimDiv (ℓ a m : ℕ) : Prop :=
  ℓ.Prime ∧ ℓ ∣ a ^ m - 1 ∧ ∀ k : ℕ, 0 < k → k < m → ¬ ℓ ∣ a ^ k - 1

theorem exists_isPrimDiv {a m : ℕ} (ha : 3 ≤ a) (hm : 3 ≤ m) : ∃ ℓ, IsPrimDiv ℓ a m := by
  obtain ⟨ℓ, h1, h2, h3⟩ := SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one ha hm
  exact ⟨ℓ, h1, h2, h3⟩

theorem pow_two_mul_sub_one (a k : ℕ) : a ^ (2 * k) - 1 = (a ^ k - 1) * (a ^ k + 1) := by
  rcases Nat.eq_zero_or_pos (a ^ k) with h0 | hpos
  · rw [mul_comm 2 k, pow_mul, h0]
    simp
  · have h1 : 1 ≤ a ^ k := hpos
    have h2 : 1 ≤ a ^ (2 * k) := by rw [mul_comm 2 k, pow_mul]; nlinarith
    zify [h1, h2]
    rw [mul_comm 2 k, pow_mul]
    ring

namespace IsPrimDiv

variable {ℓ a m : ℕ}

theorem orderOf_eq (h : IsPrimDiv ℓ a m) (ha : 0 < a) (hm : 0 < m) :
    orderOf (a : ZMod ℓ) = m := by
  rw [orderOf_eq_iff hm]
  refine ⟨(SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff ha m).1 h.2.1,
    fun k hk hk0 hk1 => ?_⟩
  exact h.2.2 k hk0 hk ((SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff ha k).2 hk1)

theorem dvd_iff (h : IsPrimDiv ℓ a m) (ha : 0 < a) (hm : 0 < m) (k : ℕ) :
    ℓ ∣ a ^ k - 1 ↔ m ∣ k := by
  rw [SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff ha, ← h.orderOf_eq ha hm]
  exact orderOf_dvd_iff_pow_eq_one.symm

theorem dvd_pow_pow_sub_one_iff (h : IsPrimDiv ℓ a m) (ha : 0 < a) (hm : 0 < m) (f k : ℕ) :
    ℓ ∣ (a ^ f) ^ k - 1 ↔ m ∣ f * k := by
  rw [← pow_mul]
  exact h.dvd_iff ha hm _

theorem dvd_two_mul_of_dvd_add_one (h : IsPrimDiv ℓ a m) (ha : 0 < a) (hm : 0 < m) {k : ℕ}
    (hk : ℓ ∣ a ^ k + 1) : m ∣ 2 * k := by
  rw [← h.dvd_iff ha hm, pow_two_mul_sub_one]
  exact Dvd.dvd.mul_left hk _

theorem dvd_of_dvd_pow_pow_add_one (h : IsPrimDiv ℓ a m) (ha : 0 < a) (hm : 0 < m) {f k : ℕ}
    (hk : ℓ ∣ (a ^ f) ^ k + 1) : m ∣ 2 * (f * k) := by
  rw [← pow_mul] at hk
  exact h.dvd_two_mul_of_dvd_add_one ha hm hk

theorem not_dvd_base (h : IsPrimDiv ℓ a m) (ha : 0 < a) (hm : 0 < m) : ¬ ℓ ∣ a := by
  intro hd
  have h1 : ℓ ∣ a ^ m := dvd_pow hd hm.ne'
  have h3 : 1 ≤ a ^ m := Nat.one_le_pow _ _ ha
  have h4 : ℓ ∣ a ^ m - (a ^ m - 1) := Nat.dvd_sub h1 h.2.1
  rw [Nat.sub_sub_self h3] at h4
  exact h.1.ne_one (Nat.dvd_one.1 h4)

theorem not_dvd_pow_base (h : IsPrimDiv ℓ a m) (ha : 0 < a) (hm : 0 < m) (k : ℕ) :
    ¬ ℓ ∣ a ^ k :=
  fun hk => h.not_dvd_base ha hm (h.1.dvd_of_dvd_pow hk)

theorem lt (h : IsPrimDiv ℓ a m) (ha : 0 < a) (hm : 0 < m) : m < ℓ := by
  have : Fact ℓ.Prime := ⟨h.1⟩
  have hne : (a : ZMod ℓ) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact h.not_dvd_base ha hm
  have hfermat : (a : ZMod ℓ) ^ (ℓ - 1) = 1 := ZMod.pow_card_sub_one_eq_one hne
  have hdvd : m ∣ ℓ - 1 := by
    rw [← h.orderOf_eq ha hm]
    exact orderOf_dvd_of_pow_eq_one hfermat
  have h2 := h.1.two_le
  have := Nat.le_of_dvd (by omega) hdvd
  omega

theorem ne_two (h : IsPrimDiv ℓ a m) (ha : Odd a) (hm : 2 ≤ m) : ℓ ≠ 2 := by
  rintro rfl
  refine h.2.2 1 one_pos (by omega) ?_
  rw [pow_one]
  obtain ⟨b, rfl⟩ := ha
  exact ⟨b, by omega⟩

theorem dvd_pow_add_one {k : ℕ} (h : IsPrimDiv ℓ a (2 * k)) (hk : 0 < k) : ℓ ∣ a ^ k + 1 := by
  have h1 := h.2.1
  rw [pow_two_mul_sub_one] at h1
  rcases (Nat.Prime.dvd_mul h.1).1 h1 with h2 | h2
  · exact absurd h2 (h.2.2 k hk (by omega))
  · exact h2

theorem dvd_pow_pow_add_one {f k : ℕ} (h : IsPrimDiv ℓ a (2 * (f * k))) (hfk : 0 < f * k) :
    ℓ ∣ (a ^ f) ^ k + 1 := by
  rw [← pow_mul]
  exact h.dvd_pow_add_one hfk

theorem dvd_pow_pow_sub_one {f k : ℕ} (h : IsPrimDiv ℓ a (f * k)) : ℓ ∣ (a ^ f) ^ k - 1 := by
  rw [← pow_mul]
  exact h.2.1

theorem not_dvd_pow_sub_one (h : IsPrimDiv ℓ a m) (ha : 0 < a) (hm : 0 < m) {f : ℕ}
    (hf : ¬ m ∣ f) : ¬ ℓ ∣ a ^ f - 1 :=
  fun hd => hf ((h.dvd_iff ha hm f).1 hd)

theorem not_dvd_pow_add_one (h : IsPrimDiv ℓ a m) (ha : 0 < a) (hm : 0 < m) {f : ℕ}
    (hf : ¬ m ∣ 2 * f) : ¬ ℓ ∣ a ^ f + 1 :=
  fun hd => hf (h.dvd_two_mul_of_dvd_add_one ha hm hd)

theorem not_dvd_small (h : IsPrimDiv ℓ a m) (ha : 0 < a) (hm : 4 ≤ m) {c : ℕ} (hc0 : 0 < c)
    (hc : c ≤ 4) : ¬ ℓ ∣ c := by
  intro hd
  have h1 := Nat.le_of_dvd hc0 hd
  have h2 := h.lt ha (by omega)
  omega

end IsPrimDiv

theorem exists_mem_dvd_of_dvd_prod {ℓ : ℕ} (hℓ : ℓ.Prime) {s : Finset ℕ} {g : ℕ → ℕ}
    (h : ℓ ∣ ∏ i ∈ s, g i) : ∃ i ∈ s, ℓ ∣ g i :=
  (Prime.dvd_finsetProd_iff hℓ.prime g).1 h

end CFSG.ComponentClassification.HarrisLit.T1.P51e
