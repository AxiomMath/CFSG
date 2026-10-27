module

public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

namespace Lemma13dZig

open Finset

theorem eq_one_of_sq_eq_one_of_pow_eq_one {K : Type*} [CommRing K] {x : K} {ℓ : ℕ} (hℓ : Odd ℓ)
    (h2 : x ^ 2 = 1) (hl : x ^ ℓ = 1) : x = 1 := by
  obtain ⟨m, rfl⟩ := hℓ
  have : x ^ (2 * m + 1) = x := by rw [pow_succ, pow_mul, h2, one_pow, one_mul]
  rw [← this]
  exact hl

theorem not_sq_dvd_geom_sum {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (a : ℤ)
    (h : (ℓ : ℤ) ∣ ∑ i ∈ range ℓ, a ^ i) : ¬ (ℓ : ℤ) ^ 2 ∣ ∑ i ∈ range ℓ, a ^ i := by
  have hodd : Odd ℓ := hℓ.odd_of_ne_two hℓ2
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have h1 : (ℓ : ℤ) ∣ a - 1 := by
    have h1' : (ℓ : ℤ) ∣ a ^ ℓ - 1 := by
      rw [← geom_sum_mul]
      exact Dvd.dvd.mul_right h _
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h1' ⊢
    push_cast at h1' ⊢
    rw [ZMod.pow_card] at h1'
    exact h1'
  obtain ⟨t, ht⟩ := h1
  have ha : a = 1 + ℓ * t := by linarith
  have hsq := odd_sq_dvd_geom_sum₂_sub (R := ℤ) 1 t hodd
  simp only [one_pow, mul_one] at hsq
  rw [← ha] at hsq
  intro hdiv
  have h3 : (ℓ : ℤ) ^ 2 ∣ (ℓ : ℤ) := by
    have := dvd_sub hdiv hsq
    simpa using this
  have h4 : ℓ ^ 2 ∣ ℓ := by exact_mod_cast h3
  have h5 := Nat.le_of_dvd hℓ.pos h4
  have h6 := hℓ.two_le
  nlinarith

theorem exists_prime_dvd_geom_sum {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (a : ℤ)
    (hbig : (ℓ : ℤ) < ∑ i ∈ range ℓ, a ^ i) :
    ∃ s : ℕ, s.Prime ∧ s ≠ ℓ ∧ (s : ℤ) ∣ ∑ i ∈ range ℓ, a ^ i := by
  by_contra hcon
  have hℓ2' := hℓ.two_le
  have hGpos : 0 < ∑ i ∈ range ℓ, a ^ i :=
    lt_trans (by exact_mod_cast hℓ.pos) hbig
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = ∑ i ∈ range ℓ, a ^ i :=
    ⟨(∑ i ∈ range ℓ, a ^ i).toNat, Int.toNat_of_nonneg hGpos.le⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
    omega
  have hnℓ : ℓ < n := by exact_mod_cast (hn ▸ hbig)
  have hpow : n = ℓ ^ n.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd hn0 (fun {d} hd hdn => by
      by_contra hne
      exact hcon ⟨d, hd, hne, by rw [← hn]; exact_mod_cast hdn⟩)
  set k := n.primeFactorsList.length with hk
  have hk2 : 2 ≤ k := by
    by_contra hlt
    interval_cases k
    · simp at hpow; omega
    · simp at hpow; omega
  have hℓn : (ℓ : ℤ) ^ 2 ∣ ∑ i ∈ range ℓ, a ^ i := by
    rw [← hn, hpow]
    exact_mod_cast pow_dvd_pow ℓ hk2
  have hℓd : (ℓ : ℤ) ∣ ∑ i ∈ range ℓ, a ^ i :=
    (dvd_pow_self (ℓ : ℤ) two_ne_zero).trans hℓn
  exact not_sq_dvd_geom_sum hℓ hℓ2 a hℓd hℓn

theorem props_of_prime_dvd_geom_sum {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (a : ℤ) {s : ℕ}
    (hs : s.Prime) (hsl : s ≠ ℓ) (hdvd : (s : ℤ) ∣ ∑ i ∈ range ℓ, a ^ i) :
    (s : ℤ) ∣ a ^ ℓ - 1 ∧ ¬ (s : ℤ) ∣ a ^ 2 - 1 ∧ ¬ (s : ℤ) ∣ a := by
  have hodd : Odd ℓ := hℓ.odd_of_ne_two hℓ2
  have : Fact s.Prime := ⟨hs⟩
  have h1 : (s : ℤ) ∣ a ^ ℓ - 1 := by
    rw [← geom_sum_mul]
    exact Dvd.dvd.mul_right hdvd _
  refine ⟨h1, ?_, ?_⟩
  · intro h2
    have hx1 : (a : ZMod s) ^ ℓ = 1 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h1
      push_cast at this
      exact sub_eq_zero.mp this
    have hx2 : (a : ZMod s) ^ 2 = 1 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h2
      push_cast at this
      exact sub_eq_zero.mp this
    have hx : (a : ZMod s) = 1 := eq_one_of_sq_eq_one_of_pow_eq_one hodd hx2 hx1
    have hG := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
    push_cast at hG
    rw [hx] at hG
    simp at hG
    rw [ZMod.natCast_eq_zero_iff] at hG
    exact hsl ((Nat.prime_dvd_prime_iff_eq hs hℓ).mp hG)
  · intro h2
    have h3 : (s : ℤ) ∣ a ^ ℓ := dvd_pow h2 hℓ.ne_zero
    have h4 : (s : ℤ) ∣ 1 := by
      have := dvd_sub h3 h1
      simpa using this
    have h5 : s ∣ 1 := by exact_mod_cast h4
    exact hs.one_lt.ne' (Nat.dvd_one.mp h5)

theorem mul_add_one_lt_pow {r ℓ : ℕ} (hr : 3 ≤ r) (hℓ : 3 ≤ ℓ) : ℓ * (r + 1) < r ^ ℓ + 1 := by
  induction ℓ, hℓ using Nat.le_induction with
  | base => nlinarith [Nat.mul_le_mul hr hr, Nat.mul_le_mul (Nat.mul_le_mul hr hr) hr]
  | succ n hn ih =>
    have h1 : r ≤ r ^ n := Nat.le_self_pow (by omega) r
    have h2 : r ^ (n + 1) = r * r ^ n := by ring
    nlinarith

theorem lt_geom_sum_natCast {r ℓ : ℕ} (hr : 2 ≤ r) (hℓ : 2 ≤ ℓ) :
    (ℓ : ℤ) < ∑ i ∈ range ℓ, (r : ℤ) ^ i := by
  have h : ∑ _i ∈ range ℓ, (1 : ℕ) < ∑ i ∈ range ℓ, r ^ i :=
    Finset.sum_lt_sum (fun i _ => Nat.one_le_pow _ _ (by omega))
      ⟨1, by simp; omega, by rw [pow_one]; omega⟩
  have h' : ℓ < ∑ i ∈ range ℓ, r ^ i := by simpa using h
  exact_mod_cast h'

theorem lt_geom_sum_neg_natCast {r ℓ : ℕ} (hr : 3 ≤ r) (hℓ : Odd ℓ) (hℓ3 : 3 ≤ ℓ) :
    (ℓ : ℤ) < ∑ i ∈ range ℓ, (-(r : ℤ)) ^ i := by
  have h := geom_sum_mul (-(r : ℤ)) ℓ
  rw [hℓ.neg_pow] at h
  have h2 : (∑ i ∈ range ℓ, (-(r : ℤ)) ^ i) * ((r : ℤ) + 1) = (r : ℤ) ^ ℓ + 1 := by
    linear_combination -h
  have h3 : (ℓ : ℤ) * ((r : ℤ) + 1) < (∑ i ∈ range ℓ, (-(r : ℤ)) ^ i) * ((r : ℤ) + 1) := by
    rw [h2]
    exact_mod_cast mul_add_one_lt_pow hr hℓ3
  exact lt_of_mul_lt_mul_right h3 (by positivity)

end Lemma13dZig

theorem exists_prime_dvd_pow_sub_one {r ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hr : Odd r)
    (hr3 : 3 ≤ r) :
    ∃ s : ℕ, s.Prime ∧ s ∣ r ^ ℓ - 1 ∧ ¬ s ∣ r ^ 2 - 1 ∧ s ≠ ℓ ∧ ¬ s ∣ r := by
  obtain ⟨s, hs, hsl, hdvd⟩ := Lemma13dZig.exists_prime_dvd_geom_sum hℓ hℓ2 (r : ℤ)
    (Lemma13dZig.lt_geom_sum_natCast (by omega) hℓ.two_le)
  obtain ⟨h1, h2, h3⟩ := Lemma13dZig.props_of_prime_dvd_geom_sum hℓ hℓ2 (r : ℤ) hs hsl hdvd
  refine ⟨s, hs, ?_, ?_, hsl, fun h => h3 (Int.natCast_dvd_natCast.mpr h)⟩
  · have hc : ((r ^ ℓ - 1 : ℕ) : ℤ) = (r : ℤ) ^ ℓ - 1 := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ hr.pos)]
      push_cast
      ring
    rw [← Int.natCast_dvd_natCast, hc]
    exact h1
  · have hc : ((r ^ 2 - 1 : ℕ) : ℤ) = (r : ℤ) ^ 2 - 1 := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ hr.pos)]
      push_cast
      ring
    rw [← Int.natCast_dvd_natCast, hc]
    exact h2

theorem exists_prime_dvd_pow_add_one {r ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hr : Odd r)
    (hr3 : 3 ≤ r) :
    ∃ s : ℕ, s.Prime ∧ s ∣ r ^ ℓ + 1 ∧ ¬ s ∣ r ^ 2 - 1 ∧ s ≠ ℓ ∧ ¬ s ∣ r := by
  have hodd : Odd ℓ := hℓ.odd_of_ne_two hℓ2
  obtain ⟨s, hs, hsl, hdvd⟩ := Lemma13dZig.exists_prime_dvd_geom_sum hℓ hℓ2 (-(r : ℤ))
    (Lemma13dZig.lt_geom_sum_neg_natCast hr3 hodd (by have := hℓ.two_le; omega))
  obtain ⟨h1, h2, h3⟩ := Lemma13dZig.props_of_prime_dvd_geom_sum hℓ hℓ2 (-(r : ℤ)) hs hsl hdvd
  refine ⟨s, hs, ?_, ?_, hsl, fun h => h3 ((dvd_neg).mpr (Int.natCast_dvd_natCast.mpr h))⟩
  · rw [← Int.natCast_dvd_natCast]
    have hc : (-(r : ℤ)) ^ ℓ - 1 = -((r ^ ℓ + 1 : ℕ) : ℤ) := by
      rw [hodd.neg_pow]
      push_cast
      ring
    rw [hc, dvd_neg] at h1
    exact h1
  · have hc : ((r ^ 2 - 1 : ℕ) : ℤ) = (-(r : ℤ)) ^ 2 - 1 := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ hr.pos)]
      push_cast
      ring
    rw [← Int.natCast_dvd_natCast, hc]
    exact h2

end CFSG.GH74.GLS.IVK.Proofs2
