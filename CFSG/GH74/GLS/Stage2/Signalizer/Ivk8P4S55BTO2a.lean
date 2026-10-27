module

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Data.Finset.Attr

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup

variable {M : Type*} [Group M]

theorem mem_of_pow_odd_of_pow_two {A : Subgroup M} {y : M} {m n : ℕ} (hm : Odd m)
    (h1 : y ^ m ∈ A) (h2 : y ^ 2 ^ n ∈ A) : y ∈ A := by
  have hcop : Nat.Coprime m (2 ^ n) := Nat.Coprime.pow_right n hm.coprime_two_right
  have hg : ((Nat.gcd m (2 ^ n) : ℕ) : ℤ) =
      m * Nat.gcdA m (2 ^ n) + 2 ^ n * Nat.gcdB m (2 ^ n) := by
    exact_mod_cast Nat.gcd_eq_gcd_ab m (2 ^ n)
  rw [hcop, Nat.cast_one] at hg
  have : y = (y ^ m) ^ Nat.gcdA m (2 ^ n) * (y ^ 2 ^ n) ^ Nat.gcdB m (2 ^ n) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
    push_cast
    rw [← hg, zpow_one]
  rw [this]
  exact A.mul_mem (A.zpow_mem h1 _) (A.zpow_mem h2 _)

theorem comm_mem_of_step {N X C : Subgroup M} [N.Normal]
    (hX2 : ∀ x ∈ X, ∃ n : ℕ, x ^ 2 ^ n ∈ N) {g : M} {m : ℕ} (hm : Odd m) (hgm : g ^ m = 1)
    (hgC : ∀ c ∈ C, g * c = c * g)
    (hstep : ∀ x ∈ X, ∃ c ∈ C, c ∈ X ∧ x⁻¹ * (g * x * g⁻¹) * c⁻¹ ∈ N) :
    ∀ x ∈ X, x⁻¹ * (g * x * g⁻¹) ∈ N := by
  intro x hx
  obtain ⟨c, hcC, hcX, hc⟩ := hstep x hx
  set q : M →* M ⧸ N := QuotientGroup.mk' N with hq
  have hqc : q (g * x * g⁻¹) = q x * q c := by
    have h1 : q (x⁻¹ * (g * x * g⁻¹) * c⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hc
    rw [map_mul, map_mul, map_inv, map_inv] at h1
    calc q (g * x * g⁻¹) = q x * ((q x)⁻¹ * q (g * x * g⁻¹) * (q c)⁻¹) * q c := by group
      _ = q x * q c := by rw [h1, mul_one]
  have hgc : ∀ k : ℕ, g * c ^ k * g⁻¹ = c ^ k := by
    intro k
    have : g * c = c * g := hgC c hcC
    rw [← conj_pow]
    congr 1
    calc g * c * g⁻¹ = c * g * g⁻¹ := by rw [this]
      _ = c := by group
  have hind : ∀ k : ℕ, q (g ^ k * x * (g ^ k)⁻¹) = q x * q c ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : g ^ (k + 1) * x * (g ^ (k + 1))⁻¹ = g * (g ^ k * x * (g ^ k)⁻¹) * g⁻¹ := by
        rw [pow_succ']
        group
      rw [e]
      have e2 : q (g * (g ^ k * x * (g ^ k)⁻¹) * g⁻¹) =
          q (g * x * g⁻¹) * q (g * c ^ k * g⁻¹) := by
        have h3 : q (g ^ k * x * (g ^ k)⁻¹) = q (x * c ^ k) := by rw [ih, map_mul, map_pow]
        calc q (g * (g ^ k * x * (g ^ k)⁻¹) * g⁻¹) = q g * q (g ^ k * x * (g ^ k)⁻¹) * (q g)⁻¹ := by
              rw [map_mul, map_mul, map_inv]
          _ = q g * q (x * c ^ k) * (q g)⁻¹ := by rw [h3]
          _ = q (g * x * g⁻¹) * q (g * c ^ k * g⁻¹) := by
              simp only [map_mul, map_inv]
              group
      rw [e2, hqc, hgc k, map_pow, pow_succ']
      group
  have hcm : q c ^ m = 1 := by
    have h4 := hind m
    rw [hgm, one_mul, inv_one, mul_one] at h4
    exact (mul_eq_left.mp h4.symm)
  obtain ⟨n, hn⟩ := hX2 c hcX
  have hcn : q c ^ 2 ^ n = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hn
  have hcop : Nat.Coprime m (2 ^ n) := Nat.Coprime.pow_right n hm.coprime_two_right
  have hq1 : q c = 1 := (pow_eq_one_iff_of_coprime hcop).mp ⟨hcm, hcn⟩
  have hcN : c ∈ N := (QuotientGroup.eq_one_iff _).mp hq1
  have : x⁻¹ * (g * x * g⁻¹) = (x⁻¹ * (g * x * g⁻¹) * c⁻¹) * c := by group
  rw [this]
  exact N.mul_mem hc hcN

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
