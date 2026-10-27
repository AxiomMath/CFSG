module

public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Module

variable {r e : ℕ} {E : Type} [Field E] (h : UnitaryFieldData r e E)
  {V : Type} [AddCommGroup V] [Module E V]

@[expose] def conjFixed (τ : V →ₛₗ[h.bar] V) : Submodule h.fixedField V where
  carrier := {v | τ v = v}
  add_mem' {v w} hv hw := by
    change τ (v + w) = v + w
    rw [map_add, show τ v = v from hv, show τ w = w from hw]
  zero_mem' := map_zero τ
  smul_mem' c v hv := by
    change τ ((c : E) • v) = (c : E) • v
    rw [map_smulₛₗ, h.mem_fixedField.mp c.2, show τ v = v from hv]

variable {h}

theorem mem_conjFixed {τ : V →ₛₗ[h.bar] V} {v : V} : v ∈ conjFixed h τ ↔ τ v = v :=
  Iff.rfl

theorem scalar_decomp {t : E} (ht : h.bar t = -t) (ht0 : t ≠ 0) (h2 : (2 : E) ≠ 0) (a : E) :
    2⁻¹ * (a + h.bar a) ∈ h.fixedField ∧ (2 * t)⁻¹ * (a - h.bar a) ∈ h.fixedField ∧
      a = 2⁻¹ * (a + h.bar a) + t * ((2 * t)⁻¹ * (a - h.bar a)) := by
  refine ⟨?_, ?_, by field_simp; ring⟩
  · rw [h.mem_fixedField, map_mul, map_add, h.bar_bar, map_inv₀, map_ofNat, add_comm (h.bar a)]
  · rw [h.mem_fixedField, map_mul, map_sub, h.bar_bar, map_inv₀, map_mul, map_ofNat, ht]
    field_simp
    ring

variable {τ : V →ₛₗ[h.bar] V} (hττ : ∀ v, τ (τ v) = v)

include hττ

theorem half_add_mem (v : V) : (2⁻¹ : E) • (v + τ v) ∈ conjFixed h τ := by
  rw [mem_conjFixed, map_smulₛₗ, map_add, hττ, map_inv₀, map_ofNat, add_comm]

theorem sub_div_mem {t : E} (ht : h.bar t = -t) (v : V) :
    (2 * t)⁻¹ • (v - τ v) ∈ conjFixed h τ := by
  rw [mem_conjFixed, map_smulₛₗ, map_sub, hττ, map_inv₀, map_mul, map_ofNat, ht, mul_neg,
    inv_neg, neg_smul, ← smul_neg, neg_sub]

omit hττ in
theorem decomp_eq {t : E} (ht0 : t ≠ 0) (h2 : (2 : E) ≠ 0) (v : V) :
    v = (2⁻¹ : E) • (v + τ v) + t • ((2 * t)⁻¹ • (v - τ v)) := by
  have h1 : t * (2 * t)⁻¹ = 2⁻¹ := by field_simp
  rw [smul_smul, h1, ← smul_add, add_add_sub_cancel, ← two_smul E v, smul_smul,
    inv_mul_cancel₀ h2, one_smul]

omit hττ in
theorem decomp_unique {t : E} (ht : h.bar t = -t) (ht0 : t ≠ 0) (h2 : (2 : E) ≠ 0) {w₀ w₁ : V}
    (hw₀ : w₀ ∈ conjFixed h τ) (hw₁ : w₁ ∈ conjFixed h τ) (h0 : w₀ + t • w₁ = 0) :
    w₀ = 0 ∧ w₁ = 0 := by
  have h1 : w₀ - t • w₁ = 0 := by
    have h3 := congrArg τ h0
    rwa [map_add, map_smulₛₗ, ht, mem_conjFixed.mp hw₀, mem_conjFixed.mp hw₁, map_zero,
      neg_smul, ← sub_eq_add_neg] at h3
  have h3 : (2 * t) • w₁ = 0 := by
    have h4 : (2 * t) • w₁ = (w₀ + t • w₁) - (w₀ - t • w₁) := by
      rw [mul_smul, two_smul]
      abel
    rw [h4, h0, h1, sub_zero]
  have hw₁0 : w₁ = 0 := (smul_eq_zero.mp h3).resolve_left (mul_ne_zero h2 ht0)
  refine ⟨?_, hw₁0⟩
  rw [hw₁0, smul_zero, add_zero] at h0
  exact h0

theorem span_conjFixed {t : E} (ht : h.bar t = -t) (ht0 : t ≠ 0) (h2 : (2 : E) ≠ 0) :
    Submodule.span E (conjFixed h τ : Set V) = ⊤ := by
  refine eq_top_iff.mpr fun v _ => ?_
  rw [decomp_eq (τ := τ) ht0 h2 v]
  exact add_mem (Submodule.subset_span (half_add_mem hττ v))
    (Submodule.smul_mem _ _ (Submodule.subset_span (sub_div_mem hττ ht v)))

omit hττ in
theorem linearIndependent_conjFixed {t : E} (ht : h.bar t = -t) (ht0 : t ≠ 0)
    (h2 : (2 : E) ≠ 0) {ι : Type*} (b : Basis ι h.fixedField (conjFixed h τ)) :
    LinearIndependent E (fun i => (b i : V)) := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  obtain ⟨x, hx⟩ : ∃ x : ι → h.fixedField,
      ∀ j, (x j : E) = 2⁻¹ * (g j + h.bar (g j)) :=
    ⟨fun j => ⟨_, (scalar_decomp ht ht0 h2 (g j)).1⟩, fun _ => rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ι → h.fixedField,
      ∀ j, (y j : E) = (2 * t)⁻¹ * (g j - h.bar (g j)) :=
    ⟨fun j => ⟨_, (scalar_decomp ht ht0 h2 (g j)).2.1⟩, fun _ => rfl⟩
  have hg' : ((∑ j ∈ s, x j • b j : conjFixed h τ) : V) +
      t • ((∑ j ∈ s, y j • b j : conjFixed h τ) : V) = 0 := by
    rw [← hg, Submodule.coe_sum, Submodule.coe_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, Submodule.coe_smul, Subfield.smul_def, Subfield.smul_def, smul_smul,
      ← add_smul, hx, hy, ← (scalar_decomp ht ht0 h2 (g j)).2.2]
  obtain ⟨h1, h3⟩ := decomp_unique ht ht0 h2 (Submodule.coe_mem _) (Submodule.coe_mem _) hg'
  have hx0 := (linearIndependent_iff'.mp b.linearIndependent) s x
    (by rw [← Submodule.coe_eq_zero]; exact h1) i hi
  have hy0 := (linearIndependent_iff'.mp b.linearIndependent) s y
    (by rw [← Submodule.coe_eq_zero]; exact h3) i hi
  have hxi := hx i
  have hyi := hy i
  rw [hx0, ZeroMemClass.coe_zero] at hxi
  rw [hy0, ZeroMemClass.coe_zero] at hyi
  rw [(scalar_decomp ht ht0 h2 (g i)).2.2, ← hxi, ← hyi, mul_zero, add_zero]

theorem span_basis_conjFixed {t : E} (ht : h.bar t = -t) (ht0 : t ≠ 0) (h2 : (2 : E) ≠ 0)
    {ι : Type*} (b : Basis ι h.fixedField (conjFixed h τ)) :
    ⊤ ≤ Submodule.span E (Set.range fun i => (b i : V)) := by
  rw [← span_conjFixed hττ ht ht0 h2, Submodule.span_le]
  intro w hw
  exact Submodule.span_induction (p := fun x _ => ((x : conjFixed h τ) : V) ∈
      Submodule.span E (Set.range fun i => (b i : V)))
    (fun x hx => by
      obtain ⟨j, rfl⟩ := hx
      exact Submodule.subset_span ⟨j, rfl⟩)
    (Submodule.zero_mem _)
    (fun x y _ _ hx hy => by
      rw [Submodule.coe_add]
      exact add_mem hx hy)
    (fun a x _ hx => by
      rw [Submodule.coe_smul, Subfield.smul_def]
      exact Submodule.smul_mem _ _ hx)
    (b.mem_span ⟨w, hw⟩)

@[expose] noncomputable def conjFixedBasis {t : E} (ht : h.bar t = -t) (ht0 : t ≠ 0)
    (h2 : (2 : E) ≠ 0) {ι : Type*} (b : Basis ι h.fixedField (conjFixed h τ)) : Basis ι E V :=
  Basis.mk (linearIndependent_conjFixed ht ht0 h2 b) (span_basis_conjFixed hττ ht ht0 h2 b)

theorem conjFixedBasis_apply {t : E} (ht : h.bar t = -t) (ht0 : t ≠ 0) (h2 : (2 : E) ≠ 0)
    {ι : Type*} (b : Basis ι h.fixedField (conjFixed h τ)) (i : ι) :
    conjFixedBasis hττ ht ht0 h2 b i = b i :=
  Basis.mk_apply _ _ i

section Finite

variable [FiniteDimensional E V]

omit hττ in
theorem finite_conjFixed : Module.Finite h.fixedField (conjFixed h τ) := by
  have := h.finite
  have : Finite V := Module.finite_of_finite E
  exact Module.Finite.of_finite

theorem finrank_conjFixed {t : E} (ht : h.bar t = -t) (ht0 : t ≠ 0) (h2 : (2 : E) ≠ 0) :
    finrank h.fixedField (conjFixed h τ) = finrank E V := by
  have := finite_conjFixed (h := h) (τ := τ)
  rw [finrank_eq_card_basis (conjFixedBasis hττ ht ht0 h2
    (Module.finBasis h.fixedField (conjFixed h τ))), Fintype.card_fin]

theorem liftBaseChange_conjFixed_bijective {t : E} (ht : h.bar t = -t) (ht0 : t ≠ 0)
    (h2 : (2 : E) ≠ 0) :
    Function.Bijective (LinearMap.liftBaseChange E (conjFixed h τ).subtype) := by
  have := finite_conjFixed (h := h) (τ := τ)
  have heq : LinearMap.liftBaseChange E (conjFixed h τ).subtype =
      ((Algebra.TensorProduct.basis E (Module.finBasis h.fixedField (conjFixed h τ))).equiv
        (conjFixedBasis hττ ht ht0 h2 (Module.finBasis h.fixedField (conjFixed h τ)))
          (Equiv.refl _)).toLinearMap := by
    refine (Algebra.TensorProduct.basis E (Module.finBasis h.fixedField (conjFixed h τ))).ext
      fun i => ?_
    rw [Algebra.TensorProduct.basis_apply, LinearMap.liftBaseChange_tmul, one_smul,
      LinearEquiv.coe_coe, ← Algebra.TensorProduct.basis_apply, Basis.equiv_apply,
      Equiv.refl_apply, conjFixedBasis_apply]
    rfl
  rw [heq]
  exact LinearEquiv.bijective _

end Finite

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
