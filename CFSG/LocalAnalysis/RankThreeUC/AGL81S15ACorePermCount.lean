module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.ACore

open Finset

theorem pmb_three_mul_le_pow {r n : ℕ} (hr : 3 ≤ r) (hn : 3 ≤ n) : 3 * (r * n) ≤ r ^ n := by
  induction n, hn using Nat.le_induction with
  | base =>
    have h : 9 ≤ r * r := by nlinarith
    calc 3 * (r * 3) = 9 * r := by ring
      _ ≤ r * r * r := Nat.mul_le_mul_right _ h
      _ = r ^ 3 := by ring
  | succ n hn ih =>
    have h0 : n + 1 ≤ n * r := by nlinarith
    have h : 3 * (r * (n + 1)) ≤ 3 * (r * n) * r := by
      calc 3 * (r * (n + 1)) = 3 * r * (n + 1) := by ring
        _ ≤ 3 * r * (n * r) := Nat.mul_le_mul_left _ h0
        _ = 3 * (r * n) * r := by ring
    calc 3 * (r * (n + 1)) ≤ 3 * (r * n) * r := h
      _ ≤ r ^ n * r := Nat.mul_le_mul_right _ ih
      _ = r ^ (n + 1) := (pow_succ r n).symm

theorem pmb_mul_sq_le_pow {r n : ℕ} (hr : 3 ≤ r) (hn : 5 ≤ n) : r * n * (r * n) ≤ r ^ n := by
  induction n, hn using Nat.le_induction with
  | base =>
    have h3 : 27 ≤ r ^ 3 := by
      calc 27 = 3 ^ 3 := rfl
        _ ≤ r ^ 3 := Nat.pow_le_pow_left hr 3
    calc r * 5 * (r * 5) = r * r * 25 := by ring
      _ ≤ r * r * r ^ 3 := Nat.mul_le_mul_left _ (by omega)
      _ = r ^ 5 := by ring
  | succ n hn ih =>
    have h1 : (n + 1) * (n + 1) ≤ r * (n * n) := by nlinarith
    calc r * (n + 1) * (r * (n + 1)) = r * r * ((n + 1) * (n + 1)) := by ring
      _ ≤ r * r * (r * (n * n)) := Nat.mul_le_mul_left _ h1
      _ = r * n * (r * n) * r := by ring
      _ ≤ r ^ n * r := Nat.mul_le_mul_right _ ih
      _ = r ^ (n + 1) := (pow_succ r n).symm

theorem pmb_prod_mul_le_pow {ι : Type*} [Fintype ι] {r : ℕ} (hr : r ≠ 1) (f : ι → ℕ) :
    ∏ i, (r * f i) ≤ r ^ (∑ i, f i) := by
  rw [← prod_pow_eq_pow_sum]
  exact prod_le_prod fun i _ => Nat.mul_le_pow hr (f i)

theorem pmb_mul_prod_mul_le_pow {ι : Type*} [Fintype ι] {r : ℕ} [Fact r.Prime] (hr : r ≠ 2)
    (f : ι → ℕ) (hf : ∀ i, f i ≠ 1 ∧ ∃ ℓ, f i = r ^ ℓ) (hsum : 4 ≤ ∑ i, f i) (i₀ : ι) :
    r * f i₀ * ∏ i, (r * f i) ≤ r ^ (∑ i, f i) := by
  classical
  have hp : r.Prime := Fact.out
  have hr3 : 3 ≤ r := by have := hp.two_le; omega
  have hge : ∀ i, r ≤ f i := by
    intro i
    obtain ⟨h1, ℓ, hℓ⟩ := hf i
    rw [hℓ] at h1 ⊢
    exact le_self_pow (by omega) fun h0 => h1 (by rw [h0, pow_zero])
  have hmul : ∀ i, r * f i ≤ r ^ f i := fun i => Nat.mul_le_pow (by omega) (f i)
  have hP : ∀ s : Finset ι, ∏ i ∈ s, (r * f i) ≤ ∏ i ∈ s, r ^ f i := fun s =>
    prod_le_prod fun i _ => hmul i
  rw [← prod_pow_eq_pow_sum, ← mul_prod_erase _ _ (mem_univ i₀),
    ← mul_prod_erase _ (fun i => r ^ f i) (mem_univ i₀)]
  by_cases h5 : 5 ≤ f i₀
  · calc r * f i₀ * (r * f i₀ * ∏ i ∈ univ.erase i₀, r * f i)
        = r * f i₀ * (r * f i₀) * ∏ i ∈ univ.erase i₀, r * f i := by ring
      _ ≤ r ^ f i₀ * ∏ i ∈ univ.erase i₀, r ^ f i :=
        Nat.mul_le_mul (pmb_mul_sq_le_pow hr3 h5) (hP _)
  obtain ⟨-, ℓ, hℓ⟩ := hf i₀
  have hr0 : r = 3 := by
    have h4 : r ≠ 4 := fun h => by
      rw [h] at hp
      rcases hp.eq_one_or_self_of_dvd 2 ⟨2, rfl⟩ with h2 | h2 <;> omega
    have := hge i₀
    omega
  have hf0 : f i₀ = 3 := by
    have h4 : f i₀ ≠ 4 := by
      intro h
      rw [hℓ, hr0] at h
      have h2 : (2 : ℕ) ∣ 3 ^ ℓ := ⟨2, by omega⟩
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2) (by decide)
    have := hge i₀
    omega
  obtain ⟨i₁, hi₁⟩ : ∃ i₁, i₁ ≠ i₀ := by
    by_contra! h
    have : ∑ i, f i = f i₀ :=
      sum_eq_single i₀ (fun i _ hi => absurd (h i) hi) fun h0 => absurd (mem_univ i₀) h0
    omega
  have hi₁' : i₁ ∈ univ.erase i₀ := mem_erase.mpr ⟨hi₁, mem_univ _⟩
  rw [← mul_prod_erase _ _ hi₁', ← mul_prod_erase _ (fun i => r ^ f i) hi₁']
  have h3 := pmb_three_mul_le_pow hr3 ((hge i₁).trans' hr3)
  subst hr0
  rw [hf0]
  calc 3 * 3 * (3 * 3 * (3 * f i₁ * ∏ i ∈ (univ.erase i₀).erase i₁, 3 * f i))
      = 27 * (3 * (3 * f i₁) * ∏ i ∈ (univ.erase i₀).erase i₁, 3 * f i) := by ring
    _ ≤ 27 * (3 ^ f i₁ * ∏ i ∈ (univ.erase i₀).erase i₁, 3 ^ f i) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul h3 (hP _))
    _ = 3 ^ 3 * (3 ^ f i₁ * ∏ i ∈ (univ.erase i₀).erase i₁, 3 ^ f i) := by ring

end CFSG.LocalAnalysis.RankThreeUC.S15.ACore
