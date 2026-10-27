module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalThreeSimilarityCoordinates

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalThreeSimilarity

open QuadraticMap CatalogueBOrthogonal

universe u v w

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]

theorem orthogonalGroup_unit_smul (Q : QuadraticForm K V) (d : Kˣ) :
    TauCeti.QuadraticMap.orthogonalGroup ((d : K) • Q) =
      TauCeti.QuadraticMap.orthogonalGroup Q := by
  ext g
  simp only [TauCeti.QuadraticMap.mem_orthogonalGroup_iff, smul_apply, smul_eq_mul]
  constructor
  · intro h v
    exact mul_left_cancel₀ d.ne_zero (h v)
  · intro h v
    rw [h v]

@[expose] def similarityOrthogonalEquiv (Q : QuadraticForm K V)
    (R : QuadraticForm K W) (d : Kˣ) (psi : V ≃ₗ[K] W)
    (hpsi : ∀ v, Q v = (d : K) * R (psi v)) :
    TauCeti.QuadraticMap.orthogonalGroup Q ≃*
      TauCeti.QuadraticMap.orthogonalGroup R :=
  (TauCeti.QuadraticMap.orthogonalGroupCongr
    ({ toLinearEquiv := psi
       map_app' := fun v => (hpsi v).symm } : Q.IsometryEquiv ((d : K) • R))).trans
    (MulEquiv.subgroupCongr (orthogonalGroup_unit_smul R d))

theorem similarityOrthogonalEquiv_apply (Q : QuadraticForm K V)
    (R : QuadraticForm K W) (d : Kˣ) (psi : V ≃ₗ[K] W)
    (hpsi : ∀ v, Q v = (d : K) * R (psi v))
    (g : TauCeti.QuadraticMap.orthogonalGroup Q) (x : W) :
    (similarityOrthogonalEquiv Q R d psi hpsi g).val x =
      psi (g.val (psi.symm x)) := by
  simp only [similarityOrthogonalEquiv, MulEquiv.trans_apply,
    MulEquiv.subgroupCongr_apply, TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply]

theorem similarityOrthogonalEquiv_symm_apply (Q : QuadraticForm K V)
    (R : QuadraticForm K W) (d : Kˣ) (psi : V ≃ₗ[K] W)
    (hpsi : ∀ v, Q v = (d : K) * R (psi v))
    (g : TauCeti.QuadraticMap.orthogonalGroup R) (v : V) :
    ((similarityOrthogonalEquiv Q R d psi hpsi).symm g).val v =
      psi.symm (g.val (psi v)) := by
  simp only [similarityOrthogonalEquiv, MulEquiv.symm_trans_apply,
    TauCeti.QuadraticMap.coe_orthogonalGroupCongr_symm_apply,
    MulEquiv.subgroupCongr_symm_apply]

variable [Finite K] [FiniteDimensional K V]

theorem exists_trace_zero_similarity_and_orthogonal_equiv (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 3) :
    ∃ (d : Kˣ) (psi : V ≃ₗ[K] traceZeroSubmodule K)
      (e : TauCeti.QuadraticMap.orthogonalGroup Q ≃*
        TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K)),
      (∀ v, Q v = (d : K) * traceZeroForm K (psi v)) ∧
      (∀ g : TauCeti.QuadraticMap.orthogonalGroup Q,
        (e g).val = (psi.symm.trans g.val).trans psi) ∧
      (∀ g : TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K),
        (e.symm g).val = (psi.trans g.val).trans psi.symm) := by
  obtain ⟨d, psi, hpsi⟩ := exists_trace_zero_similarity hodd Q hQ hdim
  refine ⟨d, psi, similarityOrthogonalEquiv Q (traceZeroForm K) d psi hpsi, hpsi, ?_, ?_⟩
  · intro g
    apply LinearEquiv.ext
    intro x
    exact similarityOrthogonalEquiv_apply Q (traceZeroForm K) d psi hpsi g x
  · intro g
    apply LinearEquiv.ext
    intro v
    exact similarityOrthogonalEquiv_symm_apply Q (traceZeroForm K) d psi hpsi g v

theorem finite_odd_orthogonal_three_trace_zero_similarity (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 3) :
    ∃ (d : Kˣ) (psi : V ≃ₗ[K] traceZeroSubmodule K)
      (e : TauCeti.QuadraticMap.orthogonalGroup Q ≃*
        TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K)),
      (∀ v, Q v = (d : K) * -(psi v).val.det) ∧
      (∀ (g : TauCeti.QuadraticMap.orthogonalGroup Q) (X : traceZeroSubmodule K),
        (e g).val X = psi (g.val (psi.symm X))) ∧
      (∀ (g : TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K)) (v : V),
        (e.symm g).val v = psi.symm (g.val (psi v))) := by
  obtain ⟨d, psi, e, hpsi, he, he'⟩ :=
    exists_trace_zero_similarity_and_orthogonal_equiv hodd Q hQ hdim
  refine ⟨d, psi, e, ?_, ?_, ?_⟩
  · intro v
    rw [← traceZeroForm_eq_neg_det]
    exact hpsi v
  · intro g X
    rw [he g]
    rfl
  · intro g v
    rw [he' g]
    rfl

end CFSG.ComponentClassification.CatalogueBOrthogonalThreeSimilarity
