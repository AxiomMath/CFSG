module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviTrace

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module LinearMap

section Additive

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem trace_eq_trace_restrict_add_trace_mapQ (W : Submodule K V) (e : V →ₗ[K] V)
    (he : W ≤ W.comap e) :
    LinearMap.trace K V e =
      LinearMap.trace K W (e.restrict he) + LinearMap.trace K (V ⧸ W) (W.mapQ W e he) := by
  classical
  set bW := Module.finBasis K W with hbW
  set bQ := Module.finBasis K (V ⧸ W) with hbQ
  set b := Module.Basis.sumQuot bW bQ with hb
  rw [LinearMap.trace_eq_matrix_trace K b e, LinearMap.trace_eq_matrix_trace K bW,
    LinearMap.trace_eq_matrix_trace K bQ, Matrix.trace, Matrix.trace, Matrix.trace,
    Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, hb, Module.Basis.sumQuot_inl]
    rw [Module.Basis.sumQuot_repr_inl_of_mem bW bQ _ (he (bW i).2)]
    rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, hb,
      Module.Basis.sumQuot_repr_inr]
    rw [← Module.Basis.sumQuot_inr bW bQ j, Submodule.mapQ_apply]
    rfl

end Additive

section KerQuot

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

abbrev rangeInKer (N : V →ₗ[K] V) : Submodule K (ker N) := (range N).comap (ker N).subtype

omit [FiniteDimensional K V] in
theorem mem_ker_of_commute {N g : V →ₗ[K] V} (hgN : ∀ x, g (N x) = N (g x)) :
    ∀ x ∈ ker N, g x ∈ ker N := fun x hx => by
  rw [mem_ker] at hx ⊢
  rw [← hgN, hx, map_zero]

omit [FiniteDimensional K V] in
theorem mem_range_of_commute {N g : V →ₗ[K] V} (hgN : ∀ x, g (N x) = N (g x)) :
    ∀ x ∈ range N, g x ∈ range N := fun x hx => by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨g y, (hgN y).symm⟩

@[expose] noncomputable def kerQuotMap (N g : V →ₗ[K] V) (hgN : ∀ x, g (N x) = N (g x)) :
    (ker N ⧸ rangeInKer N) →ₗ[K] (ker N ⧸ rangeInKer N) :=
  (rangeInKer N).mapQ (rangeInKer N) (g.restrict (mem_ker_of_commute hgN)) fun _ hx =>
    mem_range_of_commute hgN _ hx

theorem trace_eq_trace_kerQuotMap [CharP K 2] (N g : V →ₗ[K] V) (hNN : ∀ x, N (N x) = 0)
    (hgN : ∀ x, g (N x) = N (g x)) :
    LinearMap.trace K V g = LinearMap.trace K _ (kerQuotMap N g hgN) := by
  have hRK : range N ≤ ker N := by
    rintro _ ⟨y, rfl⟩
    exact hNN y
  have hk : ker N ≤ (ker N).comap g := mem_ker_of_commute hgN
  have hr : range N ≤ (range N).comap g := mem_range_of_commute hgN
  have h1 : LinearMap.trace K (V ⧸ ker N) ((ker N).mapQ (ker N) g hk) =
      LinearMap.trace K (range N) (g.restrict hr) := by
    rw [← LinearMap.trace_conj' _ (N.quotKerEquivRange)]
    congr 1
    apply LinearMap.ext
    intro y
    obtain ⟨z, rfl⟩ := (N.quotKerEquivRange).surjective y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    apply Subtype.ext
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, Submodule.mapQ_apply, LinearMap.quotKerEquivRange_apply_mk,
      LinearMap.restrict_apply]
    exact (hgN x).symm
  have h2 : LinearMap.trace K (rangeInKer N) ((g.restrict hk).restrict fun x hx =>
      mem_range_of_commute hgN _ hx) = LinearMap.trace K (range N) (g.restrict hr) := by
    rw [← LinearMap.trace_conj' _ (Submodule.comapSubtypeEquivOfLe hRK)]
    congr 1
  have hV := trace_eq_trace_restrict_add_trace_mapQ (ker N) g hk
  have hK := trace_eq_trace_restrict_add_trace_mapQ (rangeInKer N) (g.restrict hk)
    fun x hx => mem_range_of_commute hgN _ hx
  rw [hV, h1, hK, h2]
  have h0 : LinearMap.trace K (range N) (g.restrict hr) +
      LinearMap.trace K (range N) (g.restrict hr) = 0 := CharTwo.add_self_eq_zero _
  rw [kerQuotMap]
  linear_combination h0

end KerQuot

section Plus

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open LinearPilot (autFixSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)

variable {K : Type} [Field K] [CharP K 2]

theorem projLift_apply_isometry_of_mem_autFixSubgroup {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    (hQ : ∃ v, Q v ≠ 0) (s : matrixIsometries Q) {x : matrixProjectiveDerived Q}
    (hx : x ∈ autFixSubgroup (isometryConjugationHom Q s)) (v : Fin d → K) :
    projLift hQ x (matrixLinearEquiv s.val v) = matrixLinearEquiv s.val (projLift hQ x v) := by
  have h := projLift_kappa_apply hQ (matrixIsometryInclusion Q s) x v
  have hx' : matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) x = x := hx
  rw [hx'] at h
  exact h

theorem projLift_sub_one_of_mem_autFixSubgroup {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    (hQ : ∃ v, Q v ≠ 0) (s : matrixIsometries Q) {x : matrixProjectiveDerived Q}
    (hx : x ∈ autFixSubgroup (isometryConjugationHom Q s)) (v : Fin d → K) :
    projLift hQ x ((((matrixLinearEquiv s.val : (Fin d → K) →ₗ[K] (Fin d → K))) - 1) v) =
      (((matrixLinearEquiv s.val : (Fin d → K) →ₗ[K] (Fin d → K))) - 1) (projLift hQ x v) := by
  simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, map_sub]
  rw [projLift_apply_isometry_of_mem_autFixSubgroup hQ s hx]

variable [Finite K] {n f : ℕ}

theorem spLeviSection_of_kerQuot_plus (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n)
    {X : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K))} {r : ℕ} (hr : 1 ≤ r)
    (N : (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K)) (hNN : ∀ v, N (N v) = 0)
    (hXN : ∀ x ∈ X, ∀ v, projLift (exists_coordinateQuadPlus_ne_zero (by omega)) x (N v) =
      N (projLift (exists_coordinateQuadPlus_ne_zero (by omega)) x v))
    (ρ : ↥X →* CFSG.Assembly.LowTwoRank.StatedSp r K) (hρ : Function.Surjective ρ)
    (htr : ∀ x : ↥X, spMatTrace (ρ x) = LinearMap.trace K _
      (kerQuotMap N (projLift (exists_coordinateQuadPlus_ne_zero (by omega))
        (x : matrixProjectiveDerived (coordinateQuadPlus n K)) :
          (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K)) (hXN x x.2))) :
    SpLeviSection (plusFieldPart hf hK hn) X ρ.ker :=
  spLeviSection_of_trace_eq_plus hf hK hn hr ρ hρ fun x => by
    rw [htr, ← trace_eq_trace_kerQuotMap N _ hNN]

end Plus

end CFSG.SeitzReduction.OmegaPilot
