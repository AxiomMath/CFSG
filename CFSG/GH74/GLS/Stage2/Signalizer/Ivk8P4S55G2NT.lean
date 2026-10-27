module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

theorem exists_prime_dvd_pow_sub_one_not_dvd {p q₀ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ q₀) (hq3 : 3 ≤ q₀) (hodd : Odd q₀) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ≠ p ∧ r ∣ q₀ ^ p - 1 ∧ ¬ r ∣ q₀ - 1 := by
  set N : ℕ := ∑ j ∈ Finset.range p, q₀ ^ j with hN
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hq1 : 1 ≤ q₀ := by omega
  have hgeom : q₀ ^ p - 1 = (q₀ - 1) * N := by
    have h1 : 1 ≤ q₀ ^ p := Nat.one_le_pow _ _ (by omega)
    have h2 : ((q₀ ^ p - 1 : ℕ) : ℤ) = ((q₀ - 1 : ℕ) : ℤ) * (N : ℤ) := by
      push_cast [Nat.cast_sub h1, Nat.cast_sub hq1, hN]
      exact (mul_geom_sum (q₀ : ℤ) p).symm
    exact_mod_cast h2
  have hNmod : N % 2 = 1 := by
    have hq2 : q₀ % 2 = 1 := Nat.odd_iff.mp hodd
    rw [hN, Finset.sum_nat_mod]
    have : ∀ j ∈ Finset.range p, q₀ ^ j % 2 = 1 := fun j _ => by
      rw [Nat.pow_mod, hq2]
      simp
    rw [Finset.sum_congr rfl this]
    rw [Finset.sum_const, Finset.card_range]
    simpa using Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hNge : 3 ≤ N := by
    have : q₀ ^ (p - 1) ≤ N :=
      Finset.single_le_sum (f := fun j => q₀ ^ j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (by omega))
    have h3 : q₀ ≤ q₀ ^ (p - 1) := Nat.le_self_pow (by omega) q₀
    omega
  have hN1 : N ≠ 1 := by omega
  obtain ⟨r, hrp, hrN⟩ := Nat.exists_prime_and_dvd hN1
  have hr2 : r ≠ 2 := by
    intro h
    rw [h] at hrN
    omega
  have hpnd : ¬ p ∣ q₀ ^ p - 1 := by
    intro h
    have h1 : p ∣ q₀ ^ p := dvd_pow hpq hp.ne_zero
    have h2 : 1 ≤ q₀ ^ p := Nat.one_le_pow _ _ (by omega)
    have h3 : p ∣ q₀ ^ p - (q₀ ^ p - 1) := Nat.dvd_sub h1 h
    rw [Nat.sub_sub_self h2] at h3
    exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
  have hrdvd : r ∣ q₀ ^ p - 1 := by
    rw [hgeom]
    exact Dvd.dvd.mul_left hrN _
  have hrne : r ≠ p := by
    intro h
    rw [h] at hrdvd
    exact hpnd hrdvd
  refine ⟨r, hrp, hr2, hrne, hrdvd, fun hr1 => hrne ?_⟩
  have hq0r : q₀ % r = 1 % r := by
    obtain ⟨k, hk⟩ := hr1
    have : q₀ = r * k + 1 := by omega
    rw [this, Nat.mul_add_mod]
  have hNr : N % r = p % r := by
    rw [hN, Finset.sum_nat_mod]
    have : ∀ j ∈ Finset.range p, q₀ ^ j % r = 1 % r := fun j _ => by
      rw [Nat.pow_mod, hq0r, ← Nat.pow_mod, one_pow]
    have h1r : 1 % r = 1 := Nat.mod_eq_of_lt hrp.one_lt
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, h1r]
    simp
  have hrp' : r ∣ p := by
    have h0 : N % r = 0 := Nat.mod_eq_zero_of_dvd hrN
    rw [h0] at hNr
    exact Nat.dvd_of_mod_eq_zero hNr.symm
  exact (Nat.prime_dvd_prime_iff_eq hrp hp).mp hrp'

theorem hh_pow_of_coprime {Y : Type} [Group Y] {p : ℕ} (hp : p.Prime) {φ : MulAut Y}
    (hφ : φ ^ p = 1) {i : ℕ} (hi : ¬ p ∣ i)
    (hHH : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ p → ∀ Q : Subgroup Y, IsPGroup r ↥Q →
      (∀ x ∈ Q, φ x ∈ Q) → ∀ x ∈ Q, φ x = x) :
    ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ p → ∀ Q : Subgroup Y, IsPGroup r ↥Q →
      (∀ x ∈ Q, (φ ^ i) x ∈ Q) → ∀ x ∈ Q, (φ ^ i) x = x := by
  intro r hr hr2 hrp Q hQ hinv x hx
  have hcop : Nat.Coprime i p := (Nat.Prime.coprime_iff_not_dvd hp).2 hi |>.symm
  obtain ⟨j, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hφj : (φ ^ i) ^ j = φ := by
    rw [← pow_mul, pow_eq_pow_mod _ hφ, hj.2, pow_one]
  have hinvm : ∀ (m : ℕ) (y : Y), y ∈ Q → ((φ ^ i) ^ m) y ∈ Q := by
    intro m
    induction m with
    | zero => intro y hy; simpa using hy
    | succ m ih =>
      intro y hy
      rw [pow_succ, MulAut.mul_apply]
      exact ih _ (hinv y hy)
  have hinvφ : ∀ y ∈ Q, φ y ∈ Q := by
    intro y hy
    rw [← hφj]
    exact hinvm j y hy
  have hfix := hHH r hr hr2 hrp Q hQ hinvφ x hx
  have hpow : ∀ m : ℕ, (φ ^ m) x = x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, MulAut.mul_apply, hfix, ih]
  exact hpow i

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
