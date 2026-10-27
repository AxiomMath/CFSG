module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalThreeSimilarityGroups

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.ComponentClassification.CatalogueBOrthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalThreeSimilarity

variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem odd_three_space_trace_zero_similarity (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 3) :
    (∀ X : Matrix (Fin 2) (Fin 2) K, X ∈ traceZeroSubmodule K ↔ X.trace = 0) ∧
    (∀ X : traceZeroSubmodule K, traceZeroForm K X = -X.val.det) ∧
    ∃ (d : Kˣ) (ψ : V ≃ₗ[K] traceZeroSubmodule K)
      (e : TauCeti.QuadraticMap.orthogonalGroup Q ≃*
        TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K)),
      (∀ v, Q v = (d : K) * -(ψ v).val.det) ∧
      (∀ g : V ≃ₗ[K] V, (∀ v, Q (g v) = Q v) ↔
        ∀ X : traceZeroSubmodule K, -(ψ (g (ψ.symm X))).val.det = -X.val.det) ∧
      (∀ (g : TauCeti.QuadraticMap.orthogonalGroup Q) (X : traceZeroSubmodule K),
        (e g).val X = ψ (g.val (ψ.symm X))) ∧
      (∀ (h : TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K)) (v : V),
        (e.symm h).val v = ψ.symm (h.val (ψ v))) := by
  refine ⟨fun X => Iff.rfl, traceZeroForm_eq_neg_det, ?_⟩
  obtain ⟨d, ψ, e, hψ, he, he'⟩ :=
    finite_odd_orthogonal_three_trace_zero_similarity hodd Q hQ hdim
  refine ⟨d, ψ, e, hψ, fun g => ⟨fun hg X => ?_, fun hg v => ?_⟩, he, he'⟩
  · have h := hg (ψ.symm X)
    rw [hψ, hψ, LinearEquiv.apply_symm_apply] at h
    exact mul_left_cancel₀ d.ne_zero h
  · have h := hg (ψ v)
    rw [LinearEquiv.symm_apply_apply] at h
    rw [hψ, hψ, h]

end CFSG.LocalAnalysis.ComponentInitial
