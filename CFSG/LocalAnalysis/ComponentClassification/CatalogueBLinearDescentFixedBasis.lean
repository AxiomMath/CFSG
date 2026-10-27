module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedSpan
public import Mathlib.LinearAlgebra.Dimension.Constructions

public section

namespace CFSG.ComponentClassification.CatalogueBLinearDescent

noncomputable section

universe u v

theorem exists_fixed_finrank_basis {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] [Module.Finite K V]
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (htwo : (2 : K) ≠ 0) (T : V ≃+ V)
    (hTinvolution : Function.Involutive T)
    (hTsemilinear : ∀ (a : K) (v : V), T (a • v) = sigma a • T v) :
    ∃ b : Module.Basis (Fin (Module.finrank K V)) K V, ∀ i, T (b i) = b i := by
  let s : Set V := {v : V | T v = v}
  have hspan : Submodule.span K s = ⊤ :=
    fixed_vectors_span_top sigma hsigma hne htwo T hTinvolution hTsemilinear
  have hdim : Module.finrank K (Submodule.span K s) = Module.finrank K V := by
    rw [hspan, finrank_top]
  have hchoose : ∃ f : Fin (Module.finrank K V) → V,
      (∀ i, f i ∈ s) ∧ Submodule.span K (Set.range f) = Submodule.span K s ∧
        LinearIndependent K f := by
    rw [← hdim]
    exact Submodule.exists_fun_fin_finrank_span_eq K s
  obtain ⟨f, hfixed, hsp, hli⟩ := hchoose
  have htop : ⊤ ≤ Submodule.span K (Set.range f) := by rw [hsp, hspan]
  refine ⟨Module.Basis.mk hli htop, ?_⟩
  intro i
  rw [Module.Basis.mk_apply]
  exact hfixed i

theorem exists_fixed_coordinate_basis (n : ℕ) {K : Type u} [Field K]
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (htwo : (2 : K) ≠ 0) (T : (Fin n → K) ≃+ (Fin n → K))
    (hTinvolution : Function.Involutive T)
    (hTsemilinear : ∀ (a : K) (v : Fin n → K), T (a • v) = sigma a • T v) :
    ∃ b : Module.Basis (Fin n) K (Fin n → K), ∀ i, T (b i) = b i := by
  have hdim : Module.finrank K (Fin n → K) = n := by simp
  obtain ⟨b, hb⟩ :=
    exists_fixed_finrank_basis sigma hsigma hne htwo T hTinvolution hTsemilinear
  refine ⟨b.reindex (finCongr hdim), ?_⟩
  intro i
  rw [Module.Basis.reindex_apply]
  exact hb _

end

end CFSG.ComponentClassification.CatalogueBLinearDescent
