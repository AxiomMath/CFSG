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
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open QuaternionGroup

namespace Lemma31iQuat

variable {m : ℕ}

theorem inv_a' (i : ZMod (2 * m)) : (a i : QuaternionGroup m)⁻¹ = a (-i) := by
  apply inv_eq_of_mul_eq_one_right
  rw [a_mul_a, add_neg_cancel, one_def]

theorem inv_xa' (i : ZMod (2 * m)) :
    (xa i : QuaternionGroup m)⁻¹ = xa ((m : ZMod (2 * m)) + i) := by
  apply inv_eq_of_mul_eq_one_right
  rw [xa_mul_xa]
  have h2m : ((2 * m : ℕ) : ZMod (2 * m)) = 0 := ZMod.natCast_self _
  have : (m : ZMod (2 * m)) + ((m : ZMod (2 * m)) + i) - i = ((2 * m : ℕ) : ZMod (2 * m)) := by
    push_cast
    ring
  rw [this, h2m, one_def]

theorem involution_eq (hm : m ≠ 0) (x : QuaternionGroup m) (hx : x * x = 1) (hx1 : x ≠ 1) :
    x = a (m : ZMod (2 * m)) := by
  have : NeZero m := ⟨hm⟩
  cases x with
  | a i =>
    rw [a_mul_a, one_def] at hx
    have hi : i + i = 0 := QuaternionGroup.a.inj hx
    have hi2 : (2 : ZMod (2 * m)) * i = 0 := by linear_combination hi
    have hi' : i = 0 ∨ i = (m : ZMod (2 * m)) := by
      have hv := i.val_lt
      have hi3 : ((2 * i.val : ℕ) : ZMod (2 * m)) = 0 := by
        rw [Nat.cast_mul, ZMod.natCast_zmod_val]
        simpa using hi2
      rw [ZMod.natCast_eq_zero_iff] at hi3
      obtain ⟨c, hc⟩ := hi3
      have hc2 : c < 2 := by
        by_contra hcon
        push Not at hcon
        have : 2 * m * 2 ≤ 2 * m * c := Nat.mul_le_mul_left _ hcon
        omega
      interval_cases c
      · left
        have : i.val = 0 := by omega
        rw [← ZMod.natCast_zmod_val i, this]
        simp
      · right
        have : i.val = m := by omega
        rw [← ZMod.natCast_zmod_val i, this]
    rcases hi' with rfl | rfl
    · exact absurd (by rw [one_def]) hx1
    · rfl
  | xa i =>
    exfalso
    rw [xa_mul_xa, one_def] at hx
    have h0 : (m : ZMod (2 * m)) + i - i = 0 := QuaternionGroup.a.inj hx
    have h1 : (m : ZMod (2 * m)) = 0 := by linear_combination h0
    rw [ZMod.natCast_eq_zero_iff] at h1
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) h1
    omega

theorem exists_dj_quat (hm : 2 ≤ m) (q : QuaternionGroup m)
    (hn : ∀ x : QuaternionGroup m, x * q * x⁻¹ = q ∨ x * q * x⁻¹ = q * a (m : ZMod (2 * m))) :
    ∃ δ ε : QuaternionGroup m, orderOf δ = 2 * m ∧ δ ^ m = a (m : ZMod (2 * m)) ∧
      ε * ε = a (m : ZMod (2 * m)) ∧ ε * δ * ε⁻¹ = δ⁻¹ ∧ ∃ i : ℕ, q = δ ^ i := by
  have hm0 : m ≠ 0 := by omega
  have : NeZero m := ⟨hm0⟩
  cases q with
  | a i =>
    refine ⟨a 1, xa 0, orderOf_a_one, ?_, ?_, ?_, ⟨i.val, ?_⟩⟩
    · rw [a_one_pow]
    · rw [xa_mul_xa]; simp
    · rw [inv_xa', inv_a', xa_mul_a, xa_mul_xa]
      congr 1
      have h2m : ((2 * m : ℕ) : ZMod (2 * m)) = 0 := ZMod.natCast_self _
      push_cast at h2m
      linear_combination h2m
    · rw [a_one_pow, ZMod.natCast_zmod_val]
  | xa i =>
    have h := hn (a 1)
    rw [inv_a', a_mul_xa, xa_mul_a, xa_mul_a] at h
    rcases h with h | h
    · exfalso
      have h1 := QuaternionGroup.xa.inj h
      have h2 : (2 : ZMod (2 * m)) = 0 := by linear_combination -h1
      have h3 : ((2 : ℕ) : ZMod (2 * m)) = 0 := by exact_mod_cast h2
      rw [ZMod.natCast_eq_zero_iff] at h3
      have := Nat.le_of_dvd (by norm_num) h3
      omega
    · have h1 := QuaternionGroup.xa.inj h
      have h2 : ((m + 2 : ℕ) : ZMod (2 * m)) = 0 := by
        push_cast
        linear_combination -h1
      rw [ZMod.natCast_eq_zero_iff] at h2
      have h3 := Nat.le_of_dvd (by omega) h2
      have hm2 : m = 2 := by omega
      subst hm2
      refine ⟨xa i, a 1, orderOf_xa i, ?_, ?_, ?_, ⟨1, by simp⟩⟩
      · rw [xa_sq]
      · rw [a_mul_a]
        norm_num
      · rw [inv_xa', inv_a', a_mul_xa, xa_mul_a]
        congr 1
        have h4 : (4 : ZMod (2 * 2)) = 0 := by decide
        push_cast
        linear_combination (-1 : ZMod (2 * 2)) * h4

theorem exists_dj {n : ℕ} (hn : 3 ≤ n) {G : Type} [Group G] {P₁ : Subgroup G}
    (φ : P₁ ≃* QuaternionGroup (2 ^ (n - 2))) {z u₁ : G} (hz : z ∈ P₁) (hz1 : z ≠ 1)
    (hzz : z * z = 1) (hu₁ : u₁ ∈ P₁)
    (hnorm : ∀ x ∈ P₁, x * u₁ * x⁻¹ = u₁ ∨ x * u₁ * x⁻¹ = u₁ * z) :
    ∃ d ∈ P₁, ∃ j ∈ P₁, orderOf d = 2 ^ (n - 1) ∧ d ^ 2 ^ (n - 2) = z ∧ j * j = z ∧
      j * d * j⁻¹ = d⁻¹ ∧ ∃ i : ℕ, u₁ = d ^ i := by
  set m := 2 ^ (n - 2) with hm
  have hm2 : 2 ≤ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hm0 : m ≠ 0 := by omega
  have h2m : 2 * m = 2 ^ (n - 1) := by
    rw [hm, ← pow_succ']
    congr 1
    omega
  have hzq : φ ⟨z, hz⟩ = a (m : ZMod (2 * m)) := by
    apply involution_eq hm0
    · rw [← map_mul]
      have : (⟨z, hz⟩ : P₁) * ⟨z, hz⟩ = 1 := Subtype.ext hzz
      rw [this, map_one]
    · intro h1
      apply hz1
      have := φ.injective (h1.trans (map_one φ).symm)
      exact congrArg Subtype.val this
  set q := φ ⟨u₁, hu₁⟩ with hq
  have hnormQ : ∀ x : QuaternionGroup m,
      x * q * x⁻¹ = q ∨ x * q * x⁻¹ = q * a (m : ZMod (2 * m)) := by
    intro x
    obtain ⟨x', rfl⟩ := φ.surjective x
    rcases hnorm x' x'.2 with h | h
    · left
      rw [hq, ← map_mul, ← map_inv, ← map_mul]
      congr 1
      exact Subtype.ext h
    · right
      rw [hq, ← hzq, ← map_mul, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext h
  obtain ⟨δ, ε, hδo, hδm, hεε, hεδ, i, hi⟩ := exists_dj_quat hm2 q hnormQ
  refine ⟨(φ.symm δ : P₁), (φ.symm δ).2, (φ.symm ε : P₁), (φ.symm ε).2, ?_, ?_, ?_, ?_, ⟨i, ?_⟩⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hδo, h2m]
  · have : (φ.symm δ) ^ m = ⟨z, hz⟩ := by
      apply φ.injective
      rw [map_pow, MulEquiv.apply_symm_apply, hδm, hzq]
    have := congrArg Subtype.val this
    simpa using this
  · have : (φ.symm ε) * (φ.symm ε) = ⟨z, hz⟩ := by
      apply φ.injective
      rw [map_mul, MulEquiv.apply_symm_apply, hεε, hzq]
    have := congrArg Subtype.val this
    simpa using this
  · have : (φ.symm ε) * (φ.symm δ) * (φ.symm ε)⁻¹ = (φ.symm δ)⁻¹ := by
      apply φ.injective
      rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply,
        MulEquiv.apply_symm_apply, hεδ]
    have := congrArg Subtype.val this
    simpa using this
  · have : (⟨u₁, hu₁⟩ : P₁) = (φ.symm δ) ^ i := by
      apply φ.injective
      rw [map_pow, MulEquiv.apply_symm_apply, ← hi]
    have := congrArg Subtype.val this
    simpa using this

end Lemma31iQuat

end CFSG.GH74.GLS.IVK.Proofs2
