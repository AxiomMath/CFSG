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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
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

namespace CFSG.ComponentClassification.CatFC.KGHS3

variable {K : Type*} [Field K] {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
  [Module K W]

@[expose] def stabilizerOf (φ : V →ₗ[K] W) : Subgroup (V →ₗ[K] V)ˣ where
  carrier := {g | φ ∘ₗ (g : V →ₗ[K] V) = φ}
  mul_mem' := by
    intro a b ha hb
    show φ ∘ₗ ((a * b : (V →ₗ[K] V)ˣ) : V →ₗ[K] V) = φ
    rw [Units.val_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc]
    have ha' : φ ∘ₗ (a : V →ₗ[K] V) = φ := ha
    rw [ha']
    exact hb
  one_mem' := by
    show φ ∘ₗ ((1 : (V →ₗ[K] V)ˣ) : V →ₗ[K] V) = φ
    rw [Units.val_one, Module.End.one_eq_id, LinearMap.comp_id]
  inv_mem' := by
    intro a ha
    have ha' : φ ∘ₗ (a : V →ₗ[K] V) = φ := ha
    show φ ∘ₗ ((a⁻¹ : (V →ₗ[K] V)ˣ) : V →ₗ[K] V) = φ
    have : φ ∘ₗ ((a⁻¹ : (V →ₗ[K] V)ˣ) : V →ₗ[K] V) = (φ ∘ₗ (a : V →ₗ[K] V)) ∘ₗ ((a⁻¹ : (V →ₗ[K] V)ˣ) : V →ₗ[K] V) := by
      rw [ha']
    rw [this, LinearMap.comp_assoc]
    have h1 : (a : V →ₗ[K] V) ∘ₗ ((a⁻¹ : (V →ₗ[K] V)ˣ) : V →ₗ[K] V) = LinearMap.id := by
      rw [← Module.End.mul_eq_comp, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Module.End.one_eq_id]
    rw [h1, LinearMap.comp_id]

open scoped commutatorElement

theorem stab_sub_mem_span (φ : V →ₗ[K] W) (ℓ : V)
    (hker : ∀ v, φ v = 0 → v ∈ Submodule.span K {ℓ}) (g : ↥(stabilizerOf φ)) (v : V) :
    (g.1 : V →ₗ[K] V) v - v ∈ Submodule.span K {ℓ} := by
  apply hker
  have hg : φ ∘ₗ (g.1 : V →ₗ[K] V) = φ := g.2
  have h1 : φ ((g.1 : V →ₗ[K] V) v) = φ v := LinearMap.congr_fun hg v
  rw [map_sub, h1, sub_self]

theorem stab_apply_mem_span (φ : V →ₗ[K] W) (ℓ : V)
    (hker : ∀ v, φ v = 0 → v ∈ Submodule.span K {ℓ}) (g : ↥(stabilizerOf φ)) :
    (g.1 : V →ₗ[K] V) ℓ ∈ Submodule.span K {ℓ} := by
  have h := Submodule.add_mem _ (stab_sub_mem_span φ ℓ hker g ℓ)
    (Submodule.mem_span_singleton_self ℓ)
  simpa using h

theorem stab_swap_line (φ : V →ₗ[K] W) (ℓ : V)
    (hker : ∀ v, φ v = 0 → v ∈ Submodule.span K {ℓ}) (x y : ↥(stabilizerOf φ)) :
    (x.1 : V →ₗ[K] V) ((y.1 : V →ₗ[K] V) ℓ) = (y.1 : V →ₗ[K] V) ((x.1 : V →ₗ[K] V) ℓ) := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (stab_apply_mem_span φ ℓ hker x)
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (stab_apply_mem_span φ ℓ hker y)
  have e1 : (x.1 : V →ₗ[K] V) ((y.1 : V →ₗ[K] V) ℓ) = (b * a) • ℓ := by
    rw [← hb, map_smul, ← ha, smul_smul]
  have e2 : (y.1 : V →ₗ[K] V) ((x.1 : V →ₗ[K] V) ℓ) = (a * b) • ℓ := by
    rw [← ha, map_smul, ← hb, smul_smul]
  rw [e1, e2, mul_comm]

theorem stab_apply_inv_apply (φ : V →ₗ[K] W) (z : ↥(stabilizerOf φ)) (w : V) :
    (z.1 : V →ₗ[K] V) ((((z⁻¹ : ↥(stabilizerOf φ)).1 : (V →ₗ[K] V)ˣ) : V →ₗ[K] V) w) = w := by
  have h1 : (z * z⁻¹ : ↥(stabilizerOf φ)) = 1 := mul_inv_cancel z
  have h2 : ((z.1 : (V →ₗ[K] V)ˣ) : V →ₗ[K] V) *
      (((z⁻¹ : ↥(stabilizerOf φ)).1 : (V →ₗ[K] V)ˣ) : V →ₗ[K] V) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, h1, Subgroup.coe_one, Units.val_one]
  have h3 := LinearMap.congr_fun h2 w
  rwa [Module.End.mul_apply, Module.End.one_apply] at h3

theorem stab_inv_apply_apply (φ : V →ₗ[K] W) (z : ↥(stabilizerOf φ)) (w : V) :
    ((z⁻¹ : ↥(stabilizerOf φ)).1 : V →ₗ[K] V) ((z.1 : V →ₗ[K] V) w) = w := by
  have h := stab_apply_inv_apply φ z⁻¹ w
  rwa [inv_inv] at h

@[expose] def fixingOf (φ : V →ₗ[K] W) (ℓ : V) : Subgroup ↥(stabilizerOf φ) where
  carrier := {x | (x.1 : V →ₗ[K] V) ℓ = ℓ}
  mul_mem' := by
    intro a b ha hb
    have ha' : (a.1 : V →ₗ[K] V) ℓ = ℓ := ha
    have hb' : (b.1 : V →ₗ[K] V) ℓ = ℓ := hb
    show ((a * b).1 : V →ₗ[K] V) ℓ = ℓ
    rw [Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply, hb', ha']
  one_mem' := by
    show ((1 : ↥(stabilizerOf φ)).1 : V →ₗ[K] V) ℓ = ℓ
    rw [Subgroup.coe_one, Units.val_one, Module.End.one_apply]
  inv_mem' := by
    intro a ha
    have ha' : (a.1 : V →ₗ[K] V) ℓ = ℓ := ha
    show ((a⁻¹ : ↥(stabilizerOf φ)).1 : V →ₗ[K] V) ℓ = ℓ
    have h := stab_inv_apply_apply φ a ℓ
    rwa [ha'] at h

theorem stab_commutator_fixes (φ : V →ₗ[K] W) (ℓ : V)
    (hker : ∀ v, φ v = 0 → v ∈ Submodule.span K {ℓ}) (x y : ↥(stabilizerOf φ)) :
    ((⁅x, y⁆ : ↥(stabilizerOf φ)).1 : V →ₗ[K] V) ℓ = ℓ := by
  simp only [commutatorElement_def, Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply]
  rw [stab_swap_line φ ℓ hker x⁻¹ y⁻¹, stab_apply_inv_apply φ y, stab_apply_inv_apply φ x]

theorem stab_fixing_mul_comm (φ : V →ₗ[K] W) (ℓ : V)
    (hker : ∀ v, φ v = 0 → v ∈ Submodule.span K {ℓ}) (x y : ↥(stabilizerOf φ))
    (hx : (x.1 : V →ₗ[K] V) ℓ = ℓ) (hy : (y.1 : V →ₗ[K] V) ℓ = ℓ) : x * y = y * x := by
  apply Subtype.ext
  apply Units.ext
  apply LinearMap.ext
  intro v
  simp only [Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply]
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (stab_sub_mem_span φ ℓ hker x v)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (stab_sub_mem_span φ ℓ hker y v)
  have hxv : (x.1 : V →ₗ[K] V) v = v + a • ℓ := by rw [ha]; abel
  have hyv : (y.1 : V →ₗ[K] V) v = v + c • ℓ := by rw [hc]; abel
  rw [hyv, hxv]
  simp only [map_add, map_smul, hx, hy]
  rw [hxv, hyv]
  abel

theorem isSolvable_stabilizerOf (φ : V →ₗ[K] W) (ℓ : V)
    (hker : ∀ v, φ v = 0 → v ∈ Submodule.span K {ℓ}) :
    Group.IsSolvable ↥(stabilizerOf φ) := by
  have hD : derivedSeries ↥(stabilizerOf φ) 1 ≤ fixingOf φ ℓ := by
    show ⁅(⊤ : Subgroup ↥(stabilizerOf φ)), ⊤⁆ ≤ fixingOf φ ℓ
    exact Subgroup.commutator_le.mpr fun x _ y _ => stab_commutator_fixes φ ℓ hker x y
  have h2 : derivedSeries ↥(stabilizerOf φ) 2 = ⊥ := by
    show ⁅derivedSeries ↥(stabilizerOf φ) 1, derivedSeries ↥(stabilizerOf φ) 1⁆ = ⊥
    refine le_bot_iff.mp ?_
    refine (Subgroup.commutator_mono hD hD).trans ?_
    refine Subgroup.commutator_le.mpr fun g hg h hh => ?_
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact stab_fixing_mul_comm φ ℓ hker g h hg hh
  exact ⟨⟨2, h2⟩⟩

end CFSG.ComponentClassification.CatFC.KGHS3
