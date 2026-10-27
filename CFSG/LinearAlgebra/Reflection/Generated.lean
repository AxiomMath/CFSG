module


public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

public noncomputable section
open scoped BigOperators
namespace CFSG.LinearAlgebra.Reflection

universe u v w
variable {K : Type u} [Field K]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {V : Type w} [AddCommGroup V] [Module K V]

omit [Fintype ι] [DecidableEq ι] in
theorem span_eq_top_of_scalar_mem_reflection_generated
    (h : ι → V) (α : ι → Module.Dual K V) (σ : ι → V ≃ₗ[K] V)
    (hσ : ∀ i v, σ i v = v - α i v • h i)
    (s : V ≃ₗ[K] V) (hs : s ∈ Subgroup.closure (Set.range σ))
    (c : K) (hc : c ≠ 1) (hsc : ∀ v, s v = c • v) :
    Submodule.span K (Set.range h) = ⊤ := by
  classical
  let H := Submodule.span K (Set.range h)
  have hdisp : ∀ t ∈ Subgroup.closure (Set.range σ), ∀ v, t v - v ∈ H := by
    intro t ht
    induction ht using Subgroup.closure_induction with
    | mem t ht =>
      obtain ⟨i, rfl⟩ := ht
      intro v
      rw [hσ, sub_sub_cancel_left]
      exact H.neg_mem (H.smul_mem _ (Submodule.subset_span (Set.mem_range_self i)))
    | one => intro v; simp
    | mul a b _ _ ha hb =>
      intro v
      rw [LinearEquiv.mul_apply, show a (b v) - v = (a (b v) - b v) + (b v - v) by abel]
      exact H.add_mem (ha (b v)) (hb v)
    | inv a _ ha =>
      intro v
      change a.symm v - v ∈ H
      have hv := H.neg_mem (ha (a.symm v))
      simpa only [LinearEquiv.apply_symm_apply, neg_sub] using hv
  rw [eq_top_iff]
  intro v hv
  have hd := hdisp s hs v
  rw [hsc] at hd
  have hd' : (c - 1) • v ∈ H := by simpa only [sub_smul, one_smul] using hd
  have he := H.smul_mem (c - 1)⁻¹ hd'
  simpa only [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hc), one_smul] using he

omit [Fintype ι] [DecidableEq ι] in
theorem common_kernel_eq_zero_of_scalar_mem_reflection_generated
    (h : ι → V) (α : ι → Module.Dual K V) (σ : ι → V ≃ₗ[K] V)
    (hσ : ∀ i v, σ i v = v - α i v • h i)
    (s : V ≃ₗ[K] V) (hs : s ∈ Subgroup.closure (Set.range σ))
    (c : K) (hc : c ≠ 1) (hsc : ∀ v, s v = c • v) :
    ∀ v, (∀ i, α i v = 0) → v = 0 := by
  intro v hv
  have hfix : ∀ t ∈ Subgroup.closure (Set.range σ), t v = v := by
    intro t ht
    induction ht using Subgroup.closure_induction with
    | mem t ht =>
      obtain ⟨i, rfl⟩ := ht
      rw [hσ, hv, zero_smul, sub_zero]
    | one => rfl
    | mul a b _ _ ha hb => rw [LinearEquiv.mul_apply, hb, ha]
    | inv a _ ha =>
      change a.symm v = v
      apply a.injective
      rw [LinearEquiv.apply_symm_apply, ha]
  have hz : (c - 1) • v = 0 := by
    rw [sub_smul, one_smul, ← hsc, hfix s hs, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc)

end CFSG.LinearAlgebra.Reflection
