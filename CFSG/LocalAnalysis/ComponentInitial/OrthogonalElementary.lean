module

public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def orthElementaryMap (Q : QuadraticForm K V) (u v : V) : V →ₗ[K] V :=
  eichlerLin Q u v

theorem orthElementaryMap_apply (Q : QuadraticForm K V) (u v x : V) :
    orthElementaryMap Q u v x =
      x + polar Q x u • v - polar Q x v • u - (Q v * polar Q x u) • u := by
  rw [orthElementaryMap, eichlerLin_apply, add_smul]
  abel

theorem orthogonal_elementary_addition (Q : QuadraticForm K V) {u v w : V} (hu : Q u = 0)
    (hv : polar Q u v = 0) (hw : polar Q u w = 0) :
    orthElementaryMap Q u 0 = LinearMap.id ∧
      (orthElementaryMap Q u v).comp (orthElementaryMap Q u w) = orthElementaryMap Q u (v + w) ∧
      (orthElementaryMap Q u v).comp (orthElementaryMap Q u (-v)) = LinearMap.id ∧
      (orthElementaryMap Q u (-v)).comp (orthElementaryMap Q u v) = LinearMap.id := by
  have hv' : polar Q u (-v) = 0 := by rw [polar_neg_right, hv, neg_zero]
  have hzero : orthElementaryMap Q u 0 = LinearMap.id :=
    LinearMap.ext fun x => eichlerLin_zero_right Q u x
  refine ⟨hzero, LinearMap.ext fun x => eichlerLin_comp hu hv hw x, ?_, ?_⟩
  · refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, orthElementaryMap, orthElementaryMap, eichlerLin_comp hu hv hv',
      add_neg_cancel, eichlerLin_zero_right, LinearMap.id_apply]
  · refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, orthElementaryMap, orthElementaryMap, eichlerLin_comp hu hv' hv,
      neg_add_cancel, eichlerLin_zero_right, LinearMap.id_apply]

theorem orthogonal_elementary_isometry (Q : QuadraticForm K V) {u v : V} (hu : Q u = 0)
    (hv : polar Q u v = 0) :
    ∃ e : V ≃ₗ[K] V, (e : V →ₗ[K] V) = orthElementaryMap Q u v ∧ ∀ x, Q (e x) = Q x :=
  ⟨eichler Q u v, LinearMap.ext fun x => eichler_apply hu hv x, fun x => by
    rw [eichler_apply hu hv]
    exact map_eichlerLin hu hv x⟩

@[expose] def orthElementaryGroup (Q : QuadraticForm K V) : Subgroup (V ≃ₗ[K] V) :=
  elementaryGroup Q

@[expose] def orthRootGroup (Q : QuadraticForm K V) (u : V) : Subgroup (V ≃ₗ[K] V) :=
  rootGroup Q u

theorem mem_orthElementaryGroup_gen (Q : QuadraticForm K V) {u v : V} (hu : Q u = 0)
    (hv : polar Q u v = 0) :
    ∃ g ∈ orthElementaryGroup Q, (g : V →ₗ[K] V) = orthElementaryMap Q u v :=
  ⟨eichler Q u v, eichler_mem_elementaryGroup Q u v, LinearMap.ext fun x => eichler_apply hu hv x⟩

theorem orthElementaryGroup_eq_closure (Q : QuadraticForm K V) :
    orthElementaryGroup Q = Subgroup.closure {g : V ≃ₗ[K] V | ∃ u v, Q u = 0 ∧ polar Q u v = 0 ∧
      (g : V →ₗ[K] V) = orthElementaryMap Q u v} := by
  rw [orthElementaryGroup, elementaryGroup]
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_)
  · rintro _ ⟨u, v, hu, hv, rfl⟩
    exact Subgroup.subset_closure ⟨u, v, hu, hv, LinearMap.ext fun x => eichler_apply hu hv x⟩
  · rintro g ⟨u, v, hu, hv, hg⟩
    have : g = eichler Q u v := LinearEquiv.ext fun x => by
      rw [eichler_apply hu hv]
      exact LinearMap.congr_fun hg x
    rw [this]
    exact Subgroup.subset_closure ⟨u, v, hu, hv, rfl⟩

theorem orthElementaryGroup_le (Q : QuadraticForm K V) :
    orthElementaryGroup Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
  elementaryGroup_le_orthogonalGroup Q

theorem mem_orthRootGroup (Q : QuadraticForm K V) {u : V} (hu : Q u = 0) {g : V ≃ₗ[K] V} :
    g ∈ orthRootGroup Q u ↔ ∃ v, polar Q u v = 0 ∧ (g : V →ₗ[K] V) = orthElementaryMap Q u v := by
  rw [orthRootGroup, mem_rootGroup]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, LinearMap.ext fun x => eichler_apply hu hv x⟩
  · rintro ⟨v, hv, hg⟩
    refine ⟨v, hv, LinearEquiv.ext fun x => ?_⟩
    rw [eichler_apply hu hv]
    exact (LinearMap.congr_fun hg x).symm

theorem orthRootGroup_le (Q : QuadraticForm K V) (u : V) :
    orthRootGroup Q u ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
  (rootGroup_le_elementaryGroup Q u).trans (elementaryGroup_le_orthogonalGroup Q)

theorem orthogonal_elementary_conjugation (Q : QuadraticForm K V) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {u v : V} (hu : Q u = 0)
    (hv : polar Q u v = 0) :
    (g : V →ₗ[K] V) ∘ₗ orthElementaryMap Q u v ∘ₗ ((g⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) =
      orthElementaryMap Q (g u) (g v) := by
  have hgu : Q (g u) = 0 := by rw [map_of_mem hg, hu]
  have hgv : polar Q (g u) (g v) = 0 := by rw [polar_map_of_mem hg, hv]
  refine LinearMap.ext fun x => ?_
  have h := congrArg (fun e : V ≃ₗ[K] V => e x) (eichler_conj hg u v)
  simp only [LinearEquiv.mul_apply] at h
  rw [eichler_apply hu hv, eichler_apply hgu hgv] at h
  simpa [orthElementaryMap, eichlerLin_apply] using h

theorem orthogonal_elementary_normality (Q : QuadraticForm K V) :
    orthElementaryGroup Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      ((orthElementaryGroup Q).subgroupOf (TauCeti.QuadraticMap.orthogonalGroup Q)).Normal :=
  ⟨elementaryGroup_le_orthogonalGroup Q, elementaryGroup_subgroupOf_normal Q⟩

theorem orthogonal_elementary_commutator (Q : QuadraticForm K V) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {u v : V} (hu : Q u = 0)
    (hv : polar Q u v = 0) (hgu : g u = u) :
    (g : V →ₗ[K] V) ∘ₗ orthElementaryMap Q u v ∘ₗ ((g⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) ∘ₗ
        orthElementaryMap Q u (-v) = orthElementaryMap Q u (g v - v) := by
  have hgv : polar Q u (g v) = 0 := by
    rw [← hgu, polar_map_of_mem hg, hv]
  have hnv : polar Q u (-v) = 0 := by rw [polar_neg_right, hv, neg_zero]
  have h := orthogonal_elementary_conjugation Q hg hu hv
  rw [hgu] at h
  have hassoc : (g : V →ₗ[K] V) ∘ₗ orthElementaryMap Q u v ∘ₗ
      ((g⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) ∘ₗ orthElementaryMap Q u (-v) =
      ((g : V →ₗ[K] V) ∘ₗ orthElementaryMap Q u v ∘ₗ ((g⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V)) ∘ₗ
        orthElementaryMap Q u (-v) := rfl
  rw [hassoc, h, sub_eq_add_neg]
  exact (orthogonal_elementary_addition Q hu hgv hnv).2.1

theorem orthogonal_elementary_parameter_identities (Q : QuadraticForm K V) :
    (∀ (u v : V) (c : K), Q u = 0 → polar Q u v = 0 →
      orthElementaryMap Q u (v + c • u) = orthElementaryMap Q u v) ∧
    (∀ (u v : V) (c : K), Q u = 0 → polar Q u v = 0 →
      orthElementaryMap Q (c • u) v = orthElementaryMap Q u (c • v)) ∧
    ∀ v : V, orthElementaryMap Q 0 v = LinearMap.id := by
  refine ⟨fun u v c hu hv => ?_, fun u v c _ _ => ?_, fun v => ?_⟩
  · have hvu : polar Q v u = 0 := by rw [polar_comm, hv]
    refine LinearMap.ext fun x => ?_
    simp only [orthElementaryMap, eichlerLin_apply]
    rw [QuadraticMap.map_add Q, map_smul_eq_sq, hu, polar_add_right, polar_smul_right_eq,
      polar_smul_right_eq, hvu]
    module
  · refine LinearMap.ext fun x => ?_
    simp only [orthElementaryMap, eichlerLin_apply]
    rw [polar_smul_right_eq, polar_smul_right_eq, map_smul_eq_sq]
    module
  · refine LinearMap.ext fun x => ?_
    simp [orthElementaryMap, eichlerLin_apply]

theorem orthogonal_elementary_fiber_transitive (Q : QuadraticForm K V) {u x y : V} {t : K}
    (hu : Q u = 0) (hxy : Q x = Q y) (hx : polar Q u x = t) (hy : polar Q u y = t)
    (ht : t ≠ 0) :
    polar Q u (t⁻¹ • (y - x)) = 0 ∧ orthElementaryMap Q u (t⁻¹ • (y - x)) x = y := by
  have hw : polar Q u (t⁻¹ • (y - x)) = 0 := by
    rw [polar_smul_right_eq, polar_sub_right, hx, hy, sub_self, mul_zero]
  refine ⟨hw, ?_⟩
  have h := eichler_apply_eq_of_polar_eq hu hxy hx hy ht
  rw [eichler_apply hu hw] at h
  exact h

end CFSG.LocalAnalysis.ComponentInitial
