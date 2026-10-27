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

namespace CFSG.Wreathed.NormalComponentLift

variable {N : Type*} [Group N]

theorem commute_of_inf_eq_bot {J R : Subgroup N} [J.Normal] [R.Normal] (h : J ⊓ R = ⊥)
    {j r : N} (hj : j ∈ J) (hr : r ∈ R) : j * r = r * j := by
  have h1 : j * r * j⁻¹ * r⁻¹ ∈ J := by
    have := (inferInstance : J.Normal).conj_mem j⁻¹ (J.inv_mem hj) r
    have h2 := J.mul_mem hj this
    simpa [mul_assoc] using h2
  have h2 : j * r * j⁻¹ * r⁻¹ ∈ R :=
    R.mul_mem ((inferInstance : R.Normal).conj_mem r hr j) (R.inv_mem hr)
  have h3 : j * r * j⁻¹ * r⁻¹ = 1 := by
    have hm : j * r * j⁻¹ * r⁻¹ ∈ J ⊓ R := ⟨h1, h2⟩
    rw [h, Subgroup.mem_bot] at hm
    exact hm
  calc j * r = (j * r * j⁻¹ * r⁻¹) * (r * j) := by group
    _ = r * j := by rw [h3, one_mul]

theorem mk_injOn_of_inf_eq_bot {J R : Subgroup N} [R.Normal] (h : J ⊓ R = ⊥) {a b : N}
    (ha : a ∈ J) (hb : b ∈ J) (hab : (QuotientGroup.mk' R a) = QuotientGroup.mk' R b) :
    a = b := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hab
  have hm : a⁻¹ * b ∈ J ⊓ R := ⟨J.mul_mem (J.inv_mem ha) hb, hab⟩
  rw [h, Subgroup.mem_bot] at hm
  calc a = a * (a⁻¹ * b) := by rw [hm, mul_one]
    _ = b := by rw [mul_inv_cancel_left]

theorem commute_iff_mk_commute {J R : Subgroup N} [J.Normal] [R.Normal] (h : J ⊓ R = ⊥)
    {j : N} (hj : j ∈ J) (y : N) :
    j * y = y * j ↔ QuotientGroup.mk' R j * QuotientGroup.mk' R y =
      QuotientGroup.mk' R y * QuotientGroup.mk' R j := by
  constructor
  · intro hjy
    rw [← map_mul, ← map_mul, hjy]
  · intro hq
    have hR : (j * y)⁻¹ * (y * j) ∈ R := by
      rw [← QuotientGroup.eq, ← QuotientGroup.mk'_apply, ← QuotientGroup.mk'_apply, map_mul,
        map_mul, hq]
    have hJ : (j * y)⁻¹ * (y * j) ∈ J := by
      have := (inferInstance : J.Normal).conj_mem j⁻¹ (J.inv_mem hj) y⁻¹
      have h2 := J.mul_mem this hj
      simpa [mul_assoc] using h2
    have hm : (j * y)⁻¹ * (y * j) ∈ J ⊓ R := ⟨hJ, hR⟩
    rw [h, Subgroup.mem_bot] at hm
    calc j * y = j * y * ((j * y)⁻¹ * (y * j)) := by rw [hm, mul_one]
      _ = y * j := by rw [mul_inv_cancel_left]

theorem mem_of_pow_two_pow [Finite N] {J R : Subgroup N} [J.Normal] [R.Normal] (h : J ⊓ R = ⊥)
    (hR : Odd (Nat.card R)) {g : N} (hg : QuotientGroup.mk' R g ∈ J.map (QuotientGroup.mk' R))
    {k : ℕ} (hk : g ^ 2 ^ k = 1) : g ∈ J := by
  obtain ⟨j, hj, hjg⟩ := hg
  have hr : g * j⁻¹ ∈ R := by
    have : (QuotientGroup.mk' R j) = QuotientGroup.mk' R g := hjg
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at this
    have h2 := R.inv_mem this
    have h3 : (j⁻¹ * g)⁻¹ = g⁻¹ * j := by group
    rw [h3] at h2
    have h4 := (inferInstance : R.Normal).conj_mem _ h2 g
    simpa [mul_assoc] using R.inv_mem h4
  set r := g * j⁻¹ with hrdef
  have hg' : g = r * j := by rw [hrdef, inv_mul_cancel_right]
  have hcomm : Commute r j := (commute_of_inf_eq_bot h hj hr).symm
  have hpow : r ^ 2 ^ k * j ^ 2 ^ k = 1 := by
    rw [← hcomm.mul_pow, ← hg', hk]
  have hrJ : r ^ 2 ^ k ∈ J := by
    have : r ^ 2 ^ k = (j ^ 2 ^ k)⁻¹ := eq_inv_of_mul_eq_one_left hpow
    rw [this]
    exact J.inv_mem (J.pow_mem hj _)
  have hr1 : r ^ 2 ^ k = 1 := by
    have hm : r ^ 2 ^ k ∈ J ⊓ R := ⟨hrJ, R.pow_mem hr _⟩
    rw [h, Subgroup.mem_bot] at hm
    exact hm
  have hro : orderOf r = 1 := by
    have h1 : orderOf r ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hr1
    have h2 : orderOf r ∣ Nat.card R := by
      rw [← Subgroup.orderOf_mk r hr]
      exact orderOf_dvd_natCard _
    exact Nat.eq_one_of_dvd_coprimes ((Nat.coprime_two_left.mpr hR).pow_left k) h1 h2
  rw [orderOf_eq_one_iff] at hro
  rw [hg', hro, one_mul]
  exact hj

@[expose] def oddPart (K : Subgroup N) (hK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) : Subgroup N where
  carrier := {g | g ∈ K ∧ Odd (orderOf g)}
  one_mem' := ⟨K.one_mem, by rw [orderOf_one]; exact odd_one⟩
  mul_mem' := by
    rintro a b ⟨ha, hao⟩ ⟨hb, hbo⟩
    refine ⟨K.mul_mem ha hb, ?_⟩
    have hc : Commute a b := hK a ha b hb
    exact Odd.of_dvd_nat (hao.mul hbo) (hc.orderOf_mul_dvd_lcm.trans (Nat.lcm_dvd_mul _ _))
  inv_mem' := by
    rintro a ⟨ha, hao⟩
    exact ⟨K.inv_mem ha, by rw [orderOf_inv]; exact hao⟩

theorem mem_oddPart {K : Subgroup N} {hK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a} {g : N} :
    g ∈ oddPart K hK ↔ g ∈ K ∧ Odd (orderOf g) := Iff.rfl

end CFSG.Wreathed.NormalComponentLift
