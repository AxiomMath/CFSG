module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataBasic
public import CFSG.ClassicalGroups.Orthogonal.Basic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

open Matrix CatalogueBHigherLinearField CFSG.ClassicalGroups.Orthogonal
open CFSG.Assembly.LowTwoRank

universe u

variable {K : Type u} [Field K] {d : ℕ}

@[expose] def matrixConjugation (g : coordinateSemilinearGroup d K) :
    MulAut (GL (Fin d) K) :=
  (glFieldAut (Fin d) K g.right).trans (MulAut.conj g.left)

theorem matrixConjugation_apply (g : coordinateSemilinearGroup d K)
    (A : GL (Fin d) K) :
    matrixConjugation g A = g.left * glFieldAut (Fin d) K g.right A * g.left⁻¹ := rfl

theorem matrixConjugation_inl (g : coordinateSemilinearGroup d K)
    (A : GL (Fin d) K) :
    SemidirectProduct.inl (matrixConjugation g A) =
      g * SemidirectProduct.inl A * g⁻¹ := by
  apply SemidirectProduct.ext
  · simp [matrixConjugation, SemidirectProduct.mul_left, SemidirectProduct.inv_left]
  · simp

@[expose] def matrixConjugationHom :
    coordinateSemilinearGroup d K →* MulAut (GL (Fin d) K) where
  toFun := matrixConjugation
  map_one' := by
    apply MulEquiv.ext
    intro A
    apply SemidirectProduct.inl_injective (φ := glFieldAut (Fin d) K)
    rw [matrixConjugation_inl]
    simp
  map_mul' g h := by
    apply MulEquiv.ext
    intro A
    apply SemidirectProduct.inl_injective (φ := glFieldAut (Fin d) K)
    change SemidirectProduct.inl (matrixConjugation (g * h) A) =
      SemidirectProduct.inl (matrixConjugation g (matrixConjugation h A))
    rw [matrixConjugation_inl, matrixConjugation_inl, matrixConjugation_inl]
    group

theorem matrixConjugation_vector (g : coordinateSemilinearGroup d K)
    (A : GL (Fin d) K) (v : Fin d → K) :
    matrixLinearEquiv (matrixConjugation g A) v =
      coordinateSemilinearMap g
        (matrixLinearEquiv A ((coordinateSemilinearMap g).symm v)) := by
  have h := congrArg (fun x : coordinateSemilinearGroup d K => coordinateSemilinearMap x v)
    (matrixConjugation_inl g A)
  rw [coordinateSemilinearMap_mul, coordinateSemilinearMap_mul,
    coordinateSemilinearMap_inv] at h
  simpa [coordinateSemilinearMap, coordinateFieldMap] using h

@[expose] def matrixLinearIso :
    GL (Fin d) K ≃* ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
  GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin d → K))

@[expose] def matrixIsometries (Q : QuadraticForm K (Fin d → K)) :
    Subgroup (GL (Fin d) K) :=
  (TauCeti.QuadraticMap.orthogonalGroup Q).comap matrixLinearIso.toMonoidHom

theorem mem_matrixIsometries_iff (Q : QuadraticForm K (Fin d → K))
    (A : GL (Fin d) K) :
    A ∈ matrixIsometries Q ↔ ∀ v, Q (matrixLinearEquiv A v) = Q v := by
  change matrixLinearEquiv A ∈ TauCeti.QuadraticMap.orthogonalGroup Q ↔ _
  exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff

theorem matrixConjugation_mem_isometries (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) (A : GL (Fin d) K) (hA : A ∈ matrixIsometries Q) :
    matrixConjugation g.val A ∈ matrixIsometries Q := by
  rw [mem_matrixIsometries_iff] at hA ⊢
  intro v
  rw [matrixConjugation_vector, multiplier_spec, hA, ← multiplier_spec,
    AddEquiv.apply_symm_apply]

theorem matrixIsometries_invariant (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) :
    (matrixIsometries Q).map (matrixConjugation g.val).toMonoidHom =
      matrixIsometries Q := by
  ext A
  constructor
  · rintro ⟨B, hB, rfl⟩
    exact matrixConjugation_mem_isometries Q g B hB
  · intro hA
    refine ⟨matrixConjugation g⁻¹.val A,
      matrixConjugation_mem_isometries Q g⁻¹ A hA, ?_⟩
    change matrixConjugationHom g.val (matrixConjugationHom g.val⁻¹ A) = A
    rw [map_inv]
    exact (matrixConjugationHom g.val).apply_symm_apply A

theorem matrixConjugation_scalar (g : coordinateSemilinearGroup d K) (c : Kˣ) :
    matrixConjugation g (GeneralLinearGroup.scalar (Fin d) c) =
      GeneralLinearGroup.scalar (Fin d) (Units.map g.right.toMonoidHom c) := by
  rw [matrixConjugation_apply]
  change g.left * glFieldEquiv (Fin d) g.right (GeneralLinearGroup.scalar (Fin d) c) *
    g.left⁻¹ = _
  rw [glFieldEquiv_scalar]
  have hc : GeneralLinearGroup.scalar (Fin d) (Units.map g.right.toMonoidHom c) ∈
      Subgroup.center (GL (Fin d) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨Units.map g.right.toMonoidHom c, rfl⟩
  rw [Subgroup.mem_center_iff.mp hc g.left, mul_assoc, mul_inv_cancel, mul_one]

@[expose] def matrixScalars (d : ℕ) (K : Type u) [Field K] :
    Subgroup (GL (Fin d) K) := (GeneralLinearGroup.scalar (Fin d)).range

theorem matrixScalars_invariant (g : coordinateSemilinearGroup d K) :
    (matrixScalars d K).map (matrixConjugation g).toMonoidHom =
      matrixScalars d K := by
  ext A
  constructor
  · rintro ⟨B, ⟨c, rfl⟩, rfl⟩
    exact ⟨Units.map g.right.toMonoidHom c, (matrixConjugation_scalar g c).symm⟩
  · rintro ⟨c, rfl⟩
    refine ⟨GeneralLinearGroup.scalar (Fin d) (Units.map g.right.symm.toMonoidHom c),
      ⟨Units.map g.right.symm.toMonoidHom c, rfl⟩, ?_⟩
    change matrixConjugation g
      (GeneralLinearGroup.scalar (Fin d) (Units.map g.right.symm.toMonoidHom c)) = _
    rw [matrixConjugation_scalar (d := d)]
    congr 1
    apply Units.ext
    exact g.right.apply_symm_apply (c : K)

end CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
