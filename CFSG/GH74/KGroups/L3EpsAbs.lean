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

namespace CFSG.GH74.KGroups.L3Eps

open Subgroup

theorem exists_conj_mem_of_isPGroup {X : Type*} [Group X] [Finite X] {S : Subgroup X}
    (hS : IsPGroup 2 S) (hmax : ∀ T : Subgroup X, IsPGroup 2 T → S ≤ T → T ≤ S) {y : X} {k : ℕ}
    (hy : y ^ 2 ^ k = 1) : ∃ x : X, x⁻¹ * y * x ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 X := ⟨S, hS, fun {Q} hQ hSQ => le_antisymm (hmax Q hQ hSQ) hSQ⟩
  have hz : IsPGroup 2 (Subgroup.zpowers y) := by
    intro g
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy,
      one_zpow]
    rfl
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X P Q
  refine ⟨x, ?_⟩
  have hy' : y ∈ (Q : Subgroup X) := hQ (Subgroup.mem_zpowers y)
  rw [← hx] at hy'
  have := (Subgroup.mem_pointwise_smul_iff_inv_smul_mem).1 hy'
  simpa [mul_assoc] using this

theorem eq_of_pow_eq_one_of_central {G X : Type*} [Group G] [Group X] (π : G →* X) (Z : Subgroup G)
    (hZ : Z ≤ Subgroup.center G) (hZ3 : ∀ s ∈ Z, s ^ 3 = 1)
    (hπ : ∀ a b, π a = π b → a⁻¹ * b ∈ Z) {a b : G} {j : ℕ} (ha : a ^ 2 ^ j = 1)
    (hb : b ^ 2 ^ j = 1) (hab : π a = π b) : a = b := by
  set s := a⁻¹ * b with hs
  have hsZ : s ∈ Z := hπ a b hab
  have hcomm : Commute a s := Subgroup.mem_center_iff.1 (hZ hsZ) a
  have hb' : b = a * s := by rw [hs]; group
  have h1 : s ^ 2 ^ j = 1 := by
    have : b ^ 2 ^ j = a ^ 2 ^ j * s ^ 2 ^ j := by rw [hb']; exact hcomm.mul_pow _
    rw [hb, ha, one_mul] at this
    exact this.symm
  have h2 : s = 1 := by
    have h3 : s ^ Nat.gcd (2 ^ j) 3 = 1 := pow_gcd_eq_one.2 ⟨h1, hZ3 s hsZ⟩
    have : Nat.gcd (2 ^ j) 3 = 1 := by
      apply Nat.Coprime.pow_left
      norm_num
    rwa [this, pow_one] at h3
  rw [hb', h2, mul_one]

theorem mem_of_conj_fixes {X : Type*} [Group X] (hX : Subgroup.center X = ⊥) {S : Subgroup X}
    (hS : IsPGroup 2 S) (hmax : ∀ T : Subgroup X, IsPGroup 2 T → S ≤ T → T ≤ S) {z : X} {k : ℕ}
    (hz : (MulAut.conj z) ^ 2 ^ k = 1) (hfix : ∀ s ∈ S, MulAut.conj z s = s) :
    z ∈ S ∧ ∀ s ∈ S, s * z = z * s := by
  have hcomm : ∀ s ∈ S, s * z = z * s := by
    intro s hs
    have := hfix s hs
    rw [MulAut.conj_apply] at this
    calc s * z = z * s * z⁻¹ * z := by rw [this]
      _ = z * s := by group
  refine ⟨?_, hcomm⟩
  have hzk : z ^ 2 ^ k = 1 := by
    have h1 : MulAut.conj (z ^ 2 ^ k) = 1 := by rw [map_pow]; exact hz
    have h2 : z ^ 2 ^ k ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut X => φ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * z ^ 2 ^ k = (z ^ 2 ^ k * g * (z ^ 2 ^ k)⁻¹) * z ^ 2 ^ k := by rw [this]
        _ = z ^ 2 ^ k * g := by group
    rw [hX, Subgroup.mem_bot] at h2
    exact h2
  have hzp : IsPGroup 2 (Subgroup.zpowers z) := by
    intro g
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzk,
      one_zpow]
    rfl
  have hnorm : Subgroup.zpowers z ≤ Subgroup.normalizer (S : Set X) := by
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have : z * h * z⁻¹ = h := by
        have := hcomm h hh
        calc z * h * z⁻¹ = h * z * z⁻¹ := by rw [this]
          _ = h := by group
      rw [this]; exact hh
    · intro hh
      have h3 : z * (z * h * z⁻¹) = (z * h * z⁻¹) * z := (hcomm _ hh).symm
      have : h = z⁻¹ * (z * h * z⁻¹) * z := by group
      rw [this]
      have h4 : z⁻¹ * (z * h * z⁻¹) * z = z * h * z⁻¹ := by
        calc z⁻¹ * (z * h * z⁻¹) * z = z⁻¹ * ((z * h * z⁻¹) * z) := by rw [mul_assoc]
          _ = z⁻¹ * (z * (z * h * z⁻¹)) := by rw [← h3]
          _ = z * h * z⁻¹ := by group
      rw [h4]; exact hh
  have hsup := IsPGroup.to_sup_of_normal_right' hzp hS hnorm
  have := hmax _ hsup le_sup_right
  exact this (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))

theorem exists_pow_involution {G : Type*} [Group G] {σ : G} (hσ : σ ≠ 1) {k : ℕ}
    (hk : σ ^ 2 ^ k = 1) : ∃ m : ℕ, σ ^ m ≠ 1 ∧ (σ ^ m) * (σ ^ m) = 1 := by
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk)
  have he0 : e ≠ 0 := by
    rintro rfl
    exact hσ (orderOf_eq_one_iff.1 (by rw [he]; rfl))
  refine ⟨2 ^ (e - 1), ?_, ?_⟩
  · intro h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [he] at h2
    have h3 := Nat.le_of_dvd (by positivity) h2
    have h4 : 2 ^ (e - 1) < 2 ^ e := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · rw [← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel (by omega)]
    rw [← he]
    exact pow_orderOf_eq_one σ

theorem ringEquiv_pow_fix {K : Type*} [Field K] {σ : K ≃+* K} {x : K} (hx : σ x = x) (m : ℕ) : (σ ^ m) x = x := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, RingAut.mul_apply, hx, ih]


end CFSG.GH74.KGroups.L3Eps
