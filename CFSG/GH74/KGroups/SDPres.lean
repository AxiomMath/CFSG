module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.GH74.KGroups.SD

variable {R : Type*} [Group R]

structure Pres (R : Type*) [Group R] (m : ℕ) (k : ℤ) : Prop where
  ex : ∃ u τ : R, orderOf u = 2 ^ m ∧ τ ^ 2 = 1 ∧ τ⁻¹ * u * τ = u ^ k ∧
    ∀ x : R, ∃ i e : ℕ, e < 2 ∧ x = u ^ i * τ ^ e

theorem Pres.congr {S : Type*} [Group S] {m : ℕ} {k : ℤ} (h : Pres R m k) (e : R ≃* S) : Pres S m k := by
  obtain ⟨u, τ, hu, hτ, hτu, hnf⟩ := h.ex
  refine ⟨⟨e u, e τ, ?_, ?_, ?_, fun x => ?_⟩⟩
  · rw [MulEquiv.orderOf_eq, hu]
  · rw [← map_pow, hτ, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul, hτu, map_zpow]
  · obtain ⟨i, ε, hε, hx⟩ := hnf (e.symm x)
    exact ⟨i, ε, hε, by rw [← map_pow, ← map_pow, ← map_mul, ← hx, MulEquiv.apply_symm_apply]⟩

section Basic

variable {u τ : R} {m : ℕ} {k : ℤ}

theorem inv_eq_self_of_sq {τ : R} (hτ : τ ^ 2 = 1) : τ⁻¹ = τ :=
  inv_eq_of_mul_eq_one_left (by rw [← sq, hτ])

theorem tau_mul_zpow (hτ : τ ^ 2 = 1) (hτu : τ⁻¹ * u * τ = u ^ k) (j : ℤ) :
    τ * u ^ j = u ^ (k * j) * τ := by
  have hi := inv_eq_self_of_sq hτ
  have h1 : τ * u * τ⁻¹ = u ^ k := by rw [hi] at hτu ⊢; exact hτu
  have h2 : τ * u ^ j * τ⁻¹ = u ^ (k * j) := by
    rw [← conj_zpow, h1, ← zpow_mul]
  calc τ * u ^ j = τ * u ^ j * τ⁻¹ * τ := by rw [inv_mul_cancel_right]
    _ = u ^ (k * j) * τ := by rw [h2]

theorem zpow_eq_zpow_iff {u : R} {m : ℕ} (hu : orderOf u = 2 ^ m) (a b : ℤ) :
    u ^ a = u ^ b ↔ (2 : ℤ) ^ m ∣ b - a := by
  rw [zpow_eq_zpow_iff_modEq, hu, Int.modEq_iff_dvd]
  push_cast
  rfl

theorem pow_involution (hu : orderOf u = 2 ^ m) (hm : 1 ≤ m) {i : ℕ} (h : u ^ i * u ^ i = 1) :
    u ^ i = 1 ∨ u ^ i = u ^ (2 ^ (m - 1)) := by
  rw [← pow_add] at h
  have h1 : 2 ^ m ∣ i + i := hu ▸ orderOf_dvd_of_pow_eq_one h
  obtain ⟨t, ht⟩ : 2 ^ (m - 1) ∣ i := by
    have : 2 ^ m = 2 * 2 ^ (m - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [this, ← two_mul] at h1
    exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℕ) ≠ 0)).1 h1
  rcases Nat.even_or_odd' t with ⟨s, rfl | rfl⟩
  · left
    rw [ht, show 2 ^ (m - 1) * (2 * s) = 2 ^ m * s by
      rw [show 2 ^ m = 2 ^ (m - 1) * 2 by rw [← pow_succ]; congr 1; omega]; ring, pow_mul, ← hu,
      pow_orderOf_eq_one, one_pow]
  · right
    rw [ht, show 2 ^ (m - 1) * (2 * s + 1) = 2 ^ m * s + 2 ^ (m - 1) by
      rw [show 2 ^ m = 2 ^ (m - 1) * 2 by rw [← pow_succ]; congr 1; omega]; ring, pow_add, pow_mul,
      ← hu, pow_orderOf_eq_one, one_pow, one_mul]

theorem mul_tau_mul_tau (hτ : τ ^ 2 = 1) (hτu : τ⁻¹ * u * τ = u ^ k) (a b : ℤ) :
    (u ^ a * τ) * (u ^ b * τ) = u ^ (a + k * b) := by
  have h1 := tau_mul_zpow hτ hτu b
  have hτ2 : τ * τ = 1 := by rw [← sq, hτ]
  calc (u ^ a * τ) * (u ^ b * τ) = u ^ a * (τ * u ^ b) * τ := by group
    _ = u ^ a * (u ^ (k * b) * τ) * τ := by rw [h1]
    _ = u ^ a * u ^ (k * b) * (τ * τ) := by group
    _ = u ^ (a + k * b) := by rw [hτ2, mul_one, ← zpow_add]

end Basic


section Main

theorem no_normal_four {m : ℕ} {k : ℤ} (hm : 3 ≤ m) (hk : ¬ (2 : ℤ) ^ m ∣ (k - 1) ^ 2)
    (h : Pres R m k) :
    ¬ ∃ a b : R, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧
      ∀ g : R, g * a * g⁻¹ ∈ ({a, b, a * b} : Set R) ∧ g * b * g⁻¹ ∈ ({a, b, a * b} : Set R) := by
  obtain ⟨u, τ, hu, hτ, hτu, hnf⟩ := h.ex
  rintro ⟨a, b, ha1, hb1, hab, haa, hbb, hcomm, hnorm⟩
  have hcomm' : ∀ x ∈ ({a, b} : Set R), ∀ y ∈ ({a, b, a * b} : Set R), x * y = y * x := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · rfl
    · exact hcomm
    · have h1 : x * (x * b) = b := by rw [← mul_assoc, haa, one_mul]
      have h2 : x * b * x = b := by rw [hcomm, mul_assoc, haa, mul_one]
      rw [h1, h2]
    · exact hcomm.symm
    · rfl
    · have h1 : x * (a * x) = a := by rw [hcomm, ← mul_assoc, hbb, one_mul]
      have h2 : a * x * x = a := by rw [mul_assoc, hbb, mul_one]
      rw [h1, h2]
  have key : ∃ x ∈ ({a, b} : Set R), ∃ i : ℕ, x = u ^ i * τ := by
    obtain ⟨i, e, he, hae⟩ := hnf a
    obtain ⟨j, e', he', hbe⟩ := hnf b
    have he1 : e = 0 ∨ e = 1 := by omega
    have he1' : e' = 0 ∨ e' = 1 := by omega
    rcases he1 with rfl | rfl
    · rcases he1' with rfl | rfl
      · exfalso
        rw [pow_zero, mul_one] at hae hbe
        subst hae hbe
        rcases pow_involution hu (by omega) haa with h1 | h1
        · exact ha1 h1
        · rcases pow_involution hu (by omega) hbb with h2 | h2
          · exact hb1 h2
          · exact hab (h1.trans h2.symm)
      · exact ⟨b, by simp, j, by rw [hbe, pow_one]⟩
    · exact ⟨a, by simp, i, by rw [hae, pow_one]⟩
  obtain ⟨x, hx, i, hxi⟩ := key
  have hyx : u * x * u⁻¹ ∈ ({a, b, a * b} : Set R) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]; exact (hnorm u).1
    · rw [hx]; exact (hnorm u).2
  have hc := hcomm' x hx _ hyx
  have hcalc : u * x * u⁻¹ = u ^ ((i : ℤ) + 1 - k) * τ := by
    have h1 : τ * u ^ (-1 : ℤ) = u ^ (k * (-1)) * τ := tau_mul_zpow hτ hτu (-1)
    rw [hxi, ← zpow_natCast]
    calc u * (u ^ (i : ℤ) * τ) * u⁻¹ = u ^ ((i : ℤ) + 1) * (τ * u ^ (-1 : ℤ)) := by group
      _ = u ^ ((i : ℤ) + 1) * (u ^ (k * (-1)) * τ) := by rw [h1]
      _ = u ^ ((i : ℤ) + 1 - k) * τ := by rw [← mul_assoc, ← zpow_add]; congr 2; ring
  rw [hcalc, hxi, ← zpow_natCast, mul_tau_mul_tau hτ hτu, mul_tau_mul_tau hτ hτu,
    zpow_eq_zpow_iff hu] at hc
  apply hk
  have : (i : ℤ) + 1 - k + k * i - (i + k * ((i : ℤ) + 1 - k)) = (k - 1) ^ 2 := by ring
  rw [this] at hc
  exact hc

end Main

section Index

theorem no_abelian_index_two [Finite R] {m : ℕ} {k : ℤ} (hm : 3 ≤ m)
    (hk : ¬ (2 : ℤ) ^ m ∣ 2 * (k - 1)) (h : Pres R m k) :
    ¬ ∃ B : Subgroup R, B.index ≤ 2 ∧ (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧
      ∀ x ∈ B, x ^ (2 ^ (m - 1)) = 1 := by
  obtain ⟨u, τ, hu, hτ, hτu, hnf⟩ := h.ex
  rintro ⟨B, hidx, hab, hexp⟩
  have hu_not : u ∉ B := by
    intro huB
    have h1 := hexp u huB
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hu] at this
    have h2 : 2 ^ m ≤ 2 ^ (m - 1) := Nat.le_of_dvd (by positivity) this
    have h3 : 2 ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hτi := inv_eq_self_of_sq hτ
  have final : ∀ x : R, x ∈ B → (x = τ ∨ x = u * τ) → u ^ 2 ∈ B → False := by
    intro x hxB hx hu2
    have hcomm := hab x hxB (u ^ 2) hu2
    have h1 : τ * u ^ (2 : ℤ) = u ^ (k * 2) * τ := tau_mul_zpow hτ hτu 2
    have h2 : τ * u ^ 2 = u ^ 2 * τ := by
      rcases hx with rfl | rfl
      · exact hcomm
      · have : u * τ * u ^ 2 = u ^ 2 * (u * τ) := hcomm
        calc τ * u ^ 2 = u⁻¹ * (u * τ * u ^ 2) := by group
          _ = u⁻¹ * (u ^ 2 * (u * τ)) := by rw [this]
          _ = u ^ 2 * τ := by group
    have e2 : u ^ (2 : ℤ) = u ^ 2 := by simp
    have h3 : u ^ (k * 2) * τ = u ^ (2 : ℤ) * τ := by rw [← h1, e2, h2]
    have h4 : u ^ (k * 2) = u ^ (2 : ℤ) := mul_right_cancel h3
    rw [zpow_eq_zpow_iff hu] at h4
    apply hk
    have : (2 : ℤ) - k * 2 = -(2 * (k - 1)) := by ring
    rw [this] at h4
    exact dvd_neg.1 h4
  have hidx2 : B.index = 2 := by
    have : B.index ≠ 1 := by
      intro h1
      exact hu_not (by rw [Subgroup.index_eq_one] at h1; rw [h1]; trivial)
    have : B.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have : B.Normal := Subgroup.normal_of_index_eq_two hidx2
  have hu2 : u ^ 2 ∈ B := by
    have := Subgroup.pow_index_mem B u
    rwa [hidx2] at this
  by_cases hτB : τ ∈ B
  · exact final τ hτB (Or.inl rfl) hu2
  · obtain ⟨a, ha⟩ := (Subgroup.index_eq_two_iff).1 hidx2
    have h1 : u * a ∈ B := by
      have := ha u
      rcases this with ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · exact absurd h hu_not
    have h2 : τ * a ∈ B := by
      have := ha τ
      rcases this with ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · exact absurd h hτB
    have h3 : u * τ ∈ B := by
      have := B.mul_mem h1 (B.inv_mem h2)
      have e : u * a * (τ * a)⁻¹ = u * τ := by rw [mul_inv_rev, hτi]; group
      rwa [e] at this
    exact final (u * τ) h3 (Or.inr rfl) hu2

end Index

end CFSG.GH74.KGroups.SD
