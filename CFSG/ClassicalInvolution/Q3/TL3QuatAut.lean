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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.ClassicalInvolution.Q3

open QuaternionGroup

section QuatAut

theorem tl3_a_pow (n : ℕ) (s : ZMod (2 * n)) (k : ℕ) :
    (a s : QuaternionGroup n) ^ k = a ((k : ZMod (2 * n)) * s) := by
  induction k with
  | zero => simp [← a_zero]
  | succ k ih => rw [pow_succ, ih, a_mul_a]; congr 1; push_cast; ring

theorem tl3_phi_a {m : ℕ} (hm : 2 ≤ m) (φ : MulAut (QuaternionGroup (2 ^ m))) :
    ∃ s : ZMod (2 * 2 ^ m), ∀ k : ZMod (2 * 2 ^ m), φ (a k) = a (s * k) := by
  have hn : NeZero ((2 : ℕ) ^ m) := ⟨by positivity⟩
  have hord : orderOf (φ (a 1)) = 2 * 2 ^ m := by
    rw [MulEquiv.orderOf_eq, orderOf_a_one]
  cases h : φ (a 1) with
  | a s =>
    refine ⟨s, fun k => ?_⟩
    have hk : (a k : QuaternionGroup (2 ^ m)) = (a 1) ^ k.val := by
      rw [a_one_pow, ZMod.natCast_zmod_val]
    rw [hk, map_pow, h, tl3_a_pow, ZMod.natCast_zmod_val]
    congr 1
    ring
  | xa j =>
    rw [h, orderOf_xa] at hord
    exfalso
    have : 2 * 2 ^ m ≥ 8 := by
      have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      omega
    omega

theorem tl3_units_cube {N k : ℕ} [NeZero N] (hN : Nat.totient N ∣ 2 ^ k)
    (u : (ZMod N)ˣ) (h : u ^ 3 = 1) : u = 1 := by
  have hd1 : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one h
  have hd2 : orderOf u ∣ 2 ^ k := by
    refine (orderOf_dvd_card (G := (ZMod N)ˣ)).trans ?_
    rw [ZMod.card_units_eq_totient]
    exact hN
  have : orderOf u = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hd1 with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hd2
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd2
      omega
  exact orderOf_eq_one_iff.mp this

theorem tl3_aut_cube {m : ℕ} (hm : 2 ≤ m) (φ : MulAut (QuaternionGroup (2 ^ m)))
    (h3 : φ ^ 3 = 1) : φ = 1 := by
  have hn : NeZero ((2 : ℕ) ^ m) := ⟨by positivity⟩
  obtain ⟨s, hs⟩ := tl3_phi_a hm φ
  have hφ3 : ∀ x, φ (φ (φ x)) = x := fun x => by
    have := congrArg (fun ψ : MulAut (QuaternionGroup (2 ^ m)) => ψ x) h3
    simpa [pow_succ, MulAut.mul_apply] using this
  have hs3 : s ^ 3 = 1 := by
    have := hφ3 (a 1)
    rw [hs, hs, hs] at this
    have h1 : a (s * (s * (s * 1))) = (a 1 : QuaternionGroup (2 ^ m)) := this
    have h2 : s * (s * (s * 1)) = 1 := by injection h1
    rw [← h2]; ring
  have hs1 : s = 1 := by
    have hu : IsUnit s := IsUnit.of_pow_eq_one hs3 (by norm_num)
    obtain ⟨u, rfl⟩ := hu
    have hu3 : u ^ 3 = 1 := Units.ext (by simpa using hs3)
    have hne : NeZero (2 * 2 ^ m) := ⟨by positivity⟩
    have htot : Nat.totient (2 * 2 ^ m) ∣ 2 ^ m := by
      have : (2 * 2 ^ m : ℕ) = 2 ^ (m + 1) := by ring
      rw [this, Nat.totient_prime_pow Nat.prime_two (by omega)]
      simp
    exact congrArg Units.val (tl3_units_cube htot u hu3)
  subst hs1
  have hxa : ∃ j : ZMod (2 * 2 ^ m), φ (xa 0) = xa j := by
    cases h : φ (xa 0) with
    | xa j => exact ⟨j, rfl⟩
    | a i =>
      exfalso
      obtain ⟨y, hy⟩ := φ.surjective (xa 0)
      cases y with
      | a k => rw [hs] at hy; simp at hy
      | xa k =>
        have : (xa k : QuaternionGroup (2 ^ m)) = xa 0 * a k := by simp [xa_mul_a]
        rw [this, map_mul, h, hs] at hy
        simp at hy
  obtain ⟨j, hj⟩ := hxa
  have hxk : ∀ k : ZMod (2 * 2 ^ m), φ (xa k) = xa (j + k) := fun k => by
    have : (xa k : QuaternionGroup (2 ^ m)) = xa 0 * a k := by simp [xa_mul_a]
    rw [this, map_mul, hj, hs, xa_mul_a]; simp
  have hj3 : j = 0 := by
    have := hφ3 (xa 0)
    rw [hj, hxk, hxk] at this
    have h1 : xa (j + (j + j)) = (xa 0 : QuaternionGroup (2 ^ m)) := this
    have h2 : j + (j + j) = 0 := by injection h1
    have hcop : Nat.Coprime 3 (2 * 2 ^ m) := by
      apply Nat.Coprime.mul_right (by norm_num)
      exact Nat.Coprime.pow_right _ (by norm_num)
    have hu : IsUnit ((3 : ℕ) : ZMod (2 * 2 ^ m)) := (ZMod.isUnit_iff_coprime 3 _).mpr hcop
    have h3j : ((3 : ℕ) : ZMod (2 * 2 ^ m)) * j = 0 := by push_cast; rw [← h2]; ring
    exact (hu.mul_right_eq_zero).mp h3j
  subst hj3
  refine MulEquiv.ext fun x => ?_
  cases x with
  | a k => rw [hs]; simp
  | xa k => rw [hxk]; simp


theorem tl3_aut_pow_three {m : ℕ} (hm : 2 ≤ m) (φ : MulAut (QuaternionGroup (2 ^ m))) {k : ℕ}
    (h : φ ^ 3 ^ k = 1) : φ = 1 := by
  induction k generalizing φ with
  | zero => simpa using h
  | succ k ih =>
    refine tl3_aut_cube hm φ (ih (φ ^ 3) ?_)
    rw [← pow_mul, ← pow_succ']
    exact h

def tl3AutCongr {M N : Type*} [Group M] [Group N] (e : M ≃* N) : MulAut M →* MulAut N where
  toFun P := e.symm.trans (P.trans e)
  map_one' := by ext x; simp
  map_mul' P Q := by ext x; simp [MulAut.mul_apply]

theorem tl3AutCongr_injective {M N : Type*} [Group M] [Group N] (e : M ≃* N) :
    Function.Injective (tl3AutCongr e) := by
  intro P Q h
  ext x
  have := congrArg (fun f : MulAut N => f (e x)) h
  simpa [tl3AutCongr] using this

theorem tl3_aut_pow_three_of_equiv {M : Type*} [Group M] {m : ℕ} (hm : 2 ≤ m)
    (e : M ≃* QuaternionGroup (2 ^ m)) (P : MulAut M) {k : ℕ} (h : P ^ 3 ^ k = 1) : P = 1 := by
  apply tl3AutCongr_injective e
  rw [map_one]
  exact tl3_aut_pow_three hm _ (by rw [← map_pow, h, map_one])

end QuatAut

end CFSG.ClassicalInvolution.Q3
