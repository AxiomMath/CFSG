module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

namespace CFSG.ComponentClassification.CatFC.KGHS3

open Subgroup

variable {Y : Type*} [Group Y]

theorem odd_lift_unique (hZ : ∀ z ∈ center Y, z ^ 2 = 1) {m : ℕ} (hm : Odd m) {y y' : Y}
    (hyy : (y : Y ⧸ center Y) = y') (hy : y ^ m = 1) (hy' : y' ^ m = 1) : y = y' := by
  have he : y⁻¹ * y' ∈ center Y := by
    apply (QuotientGroup.eq_one_iff _).mp
    simp [hyy]
  set e := y⁻¹ * y' with he_def
  have hy'_eq : y' = y * e := by simp [e]
  have hcomm : Commute y e := Subgroup.mem_center_iff.mp he y
  have hmul : (y * e) ^ m = y ^ m * e ^ m := hcomm.mul_pow m
  rw [hy'_eq, hmul, hy, one_mul] at hy'
  obtain ⟨k, hk⟩ := hm
  have hee : e ^ 2 = 1 := hZ e he
  have hem : e ^ m = e := by rw [hk, pow_succ, pow_mul, hee, one_pow, one_mul]
  have he1 : e = 1 := by rw [← hem]; exact hy'
  rw [hy'_eq, he1, mul_one]

theorem odd_lift_exists (hZ : ∀ z ∈ center Y, z ^ 2 = 1) {m : ℕ} (hm : Odd m)
    {x : Y ⧸ center Y} (hx : x ^ m = 1) : ∃ y : Y, (y : Y ⧸ center Y) = x ∧ y ^ m = 1 := by
  obtain ⟨y₁, rfl⟩ := QuotientGroup.mk_surjective x
  have h1 : y₁ ^ m ∈ center Y := by
    apply (QuotientGroup.eq_one_iff _).mp
    rw [QuotientGroup.mk_pow]; exact hx
  obtain ⟨k, hk⟩ := hm
  refine ⟨y₁ ^ (m + 1), ?_, ?_⟩
  · rw [QuotientGroup.mk_pow, pow_succ, hx, one_mul]
  · have hsq := hZ _ h1
    calc (y₁ ^ (m + 1)) ^ m = (y₁ ^ m) ^ (m + 1) := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = ((y₁ ^ m) ^ 2) ^ (k + 1) := by rw [← pow_mul (y₁ ^ m) 2 (k + 1), show 2 * (k + 1) = m + 1 by omega]
      _ = 1 := by rw [hsq, one_pow]

theorem exists_C3_lift (hZ : ∀ z ∈ center Y, z ^ 2 = 1) {a b g : Y ⧸ center Y} (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1) (hab : a * b = b * a) (ha1 : a ≠ 1) (hga : g * a * g⁻¹ = b)
    (hgb : g * b * g⁻¹ = a * b) :
    ∃ a' b' g' : Y, a' ^ 3 = 1 ∧ b' ^ 3 = 1 ∧ a' * b' = b' * a' ∧ a' ≠ 1 ∧
      g' * a' * g'⁻¹ = b' ∧ g' * b' * g'⁻¹ = a' * b' := by
  have h3 : Odd 3 := by decide
  obtain ⟨a', rfl, ha'⟩ := odd_lift_exists hZ h3 ha
  obtain ⟨b', rfl, hb'⟩ := odd_lift_exists hZ h3 hb
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
  have hcomm : a' * b' = b' * a' := by
    set c := a' * b' * a'⁻¹ * b'⁻¹ with hc
    have hcc : c ∈ center Y := by
      apply (QuotientGroup.eq_one_iff _).mp
      simp only [hc, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hab]; simp
    have hc2 : c ^ 2 = 1 := hZ c hcc
    have hcz : ∀ g : Y, g * c = c * g := fun g => Subgroup.mem_center_iff.mp hcc g
    have hb_conj : a' * b' * a'⁻¹ = c * b' := by simp [hc]
    have h1 : (a' * b' * a'⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hb', mul_one, mul_inv_cancel]
    have h2 : (c * b') ^ 3 = c := by
      have hcomm' : Commute c b' := (hcz b').symm
      rw [hcomm'.mul_pow, hb', mul_one]
      calc c ^ 3 = c ^ 2 * c := by rw [pow_succ]
        _ = c := by rw [hc2, one_mul]
    rw [hb_conj, h2] at h1
    have : c = 1 := h1
    calc a' * b' = c * (b' * a') := by simp [hc, mul_assoc]
      _ = b' * a' := by rw [this, one_mul]
  refine ⟨a', b', g', ha', hb', hcomm, ?_, ?_, ?_⟩
  · intro h; apply ha1; rw [h]; simp
  · apply odd_lift_unique hZ h3
    · simpa [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using hga
    · rw [conj_pow, ha', mul_one, mul_inv_cancel]
    · exact hb'
  · apply odd_lift_unique hZ h3
    · simpa [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using hgb
    · rw [conj_pow, hb', mul_one, mul_inv_cancel]
    · rw [Commute.mul_pow (show Commute a' b' from hcomm) 3, ha', hb', mul_one]

theorem exists_C5_lift (hZ : ∀ z ∈ center Y, z ^ 2 = 1) {x y z g : Y ⧸ center Y}
    (hz : z = x * y * x⁻¹ * y⁻¹) (hz5 : z ^ 5 = 1) (hz1 : z ≠ 1) (hxz : x * z = z * x)
    (hyz : y * z = z * y) (hgz : g * z * g⁻¹ = z ^ 2) :
    ∃ x' y' z' g' w' : Y, z' ^ 5 = 1 ∧ z' ≠ 1 ∧ x' * z' = z' * x' ∧ y' * z' = z' * y' ∧
      g' * z' * g'⁻¹ = z' ^ 2 ∧ w' * x' = x' * w' ∧ w' * y' = y' * w' ∧ w' * z' = z' * w' ∧
      w' ^ 2 = 1 ∧ x' * y' * x'⁻¹ * y'⁻¹ = z' * w' := by
  have h5 : Odd 5 := by decide
  obtain ⟨z', rfl, hz'⟩ := odd_lift_exists hZ h5 hz5
  obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
  have hw : z'⁻¹ * (x' * y' * x'⁻¹ * y'⁻¹) ∈ center Y := by
    apply (QuotientGroup.eq_one_iff _).mp
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hz]
    exact inv_mul_cancel _
  have hwc : ∀ t : Y, t * (z'⁻¹ * (x' * y' * x'⁻¹ * y'⁻¹)) = (z'⁻¹ * (x' * y' * x'⁻¹ * y'⁻¹)) * t :=
    fun t => Subgroup.mem_center_iff.mp hw t
  have hcx : x' * z' * x'⁻¹ = z' := by
    apply odd_lift_unique hZ h5
    · simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hxz, mul_inv_cancel_right]
    · rw [conj_pow, hz', mul_one, mul_inv_cancel]
    · exact hz'
  have hcy : y' * z' * y'⁻¹ = z' := by
    apply odd_lift_unique hZ h5
    · simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hyz, mul_inv_cancel_right]
    · rw [conj_pow, hz', mul_one, mul_inv_cancel]
    · exact hz'
  have hcg : g' * z' * g'⁻¹ = z' ^ 2 := by
    apply odd_lift_unique hZ h5
    · simpa [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow] using hgz
    · rw [conj_pow, hz', mul_one, mul_inv_cancel]
    · rw [← pow_mul, mul_comm, pow_mul, hz', one_pow]
  refine ⟨x', y', z', g', z'⁻¹ * (x' * y' * x'⁻¹ * y'⁻¹), hz', ?_, ?_, ?_, hcg, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; apply hz1; rw [h]; simp
  · exact mul_inv_eq_iff_eq_mul.mp hcx
  · exact mul_inv_eq_iff_eq_mul.mp hcy
  · exact (hwc x').symm
  · exact (hwc y').symm
  · exact (hwc z').symm
  · exact hZ _ hw
  · exact (mul_inv_cancel_left _ _).symm

theorem exists_C11_lift (hZ : ∀ z ∈ center Y, z ^ 2 = 1) {u h : Y ⧸ center Y} (hu : u ^ 11 = 1)
    (hu1 : u ≠ 1) (hhu : h * u * h⁻¹ = u ^ 3) :
    ∃ u' h' : Y, u' ^ 11 = 1 ∧ u' ≠ 1 ∧ h' * u' * h'⁻¹ = u' ^ 3 := by
  have h11 : Odd 11 := by decide
  obtain ⟨u', rfl, hu'⟩ := odd_lift_exists hZ h11 hu
  obtain ⟨h', rfl⟩ := QuotientGroup.mk_surjective h
  refine ⟨u', h', hu', ?_, ?_⟩
  · intro h; apply hu1; rw [h]; simp
  · apply odd_lift_unique hZ h11
    · simpa [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow] using hhu
    · rw [conj_pow, hu', mul_one, mul_inv_cancel]
    · rw [← pow_mul, mul_comm, pow_mul, hu', one_pow]

end CFSG.ComponentClassification.CatFC.KGHS3
