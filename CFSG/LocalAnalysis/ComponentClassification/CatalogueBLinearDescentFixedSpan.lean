module

public import Mathlib.Algebra.Ring.Aut
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.ComponentClassification.CatalogueBLinearDescent

noncomputable section

universe u v

theorem exists_antifixed_coefficient {K : Type u} [Field K]
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) :
    ∃ a : K, a ≠ 0 ∧ sigma a = -a := by
  obtain ⟨x, hx⟩ : ∃ x : K, sigma x ≠ x := by
    by_contra h
    apply hne
    ext x
    exact not_not.mp (not_exists.mp h x)
  have hinvolution (x : K) : sigma (sigma x) = x := by
    simpa [pow_two] using DFunLike.congr_fun hsigma x
  refine ⟨x - sigma x, ?_, ?_⟩
  · exact sub_ne_zero.mpr hx.symm
  · rw [map_sub, hinvolution]
    abel

theorem fixed_vectors_span_top {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V]
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (htwo : (2 : K) ≠ 0) (T : V ≃+ V)
    (hTinvolution : Function.Involutive T)
    (hTsemilinear : ∀ (a : K) (v : V), T (a • v) = sigma a • T v) :
    Submodule.span K {v : V | T v = v} = ⊤ := by
  obtain ⟨a, ha, hsigmaa⟩ := exists_antifixed_coefficient sigma hsigma hne
  apply top_unique
  intro v _
  let W := Submodule.span K {v : V | T v = v}
  have hsymmetric : v + T v ∈ W := by
    apply Submodule.subset_span
    change T (v + T v) = v + T v
    rw [map_add, hTinvolution]
    exact add_comm _ _
  have hantisymmetric : a • (v - T v) ∈ W := by
    apply Submodule.subset_span
    change T (a • (v - T v)) = a • (v - T v)
    rw [hTsemilinear, hsigmaa, map_sub, hTinvolution]
    rw [show T v - v = -(v - T v) by abel, neg_smul, smul_neg, neg_neg]
  have hdifference : v - T v ∈ W := by
    have h := W.smul_mem a⁻¹ hantisymmetric
    simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using h
  have hdouble : (2 : K) • v ∈ W := by
    have hsum := W.add_mem hsymmetric hdifference
    have heq : (v + T v) + (v - T v) = (2 : K) • v := by
      rw [two_smul]
      abel
    rwa [heq] at hsum
  have h := W.smul_mem (2 : K)⁻¹ hdouble
  simpa only [smul_smul, inv_mul_cancel₀ htwo, one_smul] using h

end

end CFSG.ComponentClassification.CatalogueBLinearDescent
