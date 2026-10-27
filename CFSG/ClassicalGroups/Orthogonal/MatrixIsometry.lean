module

public import CFSG.Open.PGLModelDefs

public section

namespace CFSG.PGLModel

open Matrix

theorem mem_orthogonalGroup_iff {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    {Q : (ι → K) → K} {A : GL ι K} :
    A ∈ orthogonalGroup Q ↔ ∀ v : ι → K, Q ((A : Matrix ι ι K) *ᵥ v) = Q v := by
  constructor
  · intro hA
    unfold orthogonalGroup at hA
    induction hA using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => simp
    | mul x y _ _ hx hy =>
      intro v
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, hx, hy]
    | inv x _ hx =>
      intro v
      have h := hx ((↑x⁻¹ : Matrix ι ι K) *ᵥ v)
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec, eq_comm] at h
  · intro h
    unfold orthogonalGroup
    exact Subgroup.subset_closure h

private theorem map_conj_aux {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    {Q Q' : (ι → K) → K} {P : GL ι K}
    (hP : ∀ v : ι → K, Q' ((P : Matrix ι ι K) *ᵥ v) = Q v) :
    ∀ v : ι → K, Q ((P⁻¹ : GL ι K) *ᵥ v) = Q' v := by
  intro v
  have h := hP ((P⁻¹ : GL ι K) *ᵥ v)
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.one_mulVec] at h
  exact h.symm

theorem orthogonalGroup_eq_map_conj {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    {Q Q' : (ι → K) → K} (P : GL ι K) (hP : ∀ v : ι → K, Q' ((P : Matrix ι ι K) *ᵥ v) = Q v) :
    orthogonalGroup Q' = (orthogonalGroup Q).map (MulAut.conj P).toMonoidHom := by
  ext B
  rw [Subgroup.mem_map]
  constructor
  · intro hB
    rw [mem_orthogonalGroup_iff] at hB
    refine ⟨P⁻¹ * B * P, ?_, ?_⟩
    · rw [mem_orthogonalGroup_iff]
      intro v
      rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      rw [map_conj_aux hP, hB, hP]
    · change MulAut.conj P (P⁻¹ * B * P) = B
      rw [MulAut.conj_apply]
      group
  · rintro ⟨A, hA, rfl⟩
    rw [mem_orthogonalGroup_iff] at hA
    rw [mem_orthogonalGroup_iff]
    intro v
    change Q' (((P * A * P⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) = Q' v
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [hP, hA ((P⁻¹ : GL ι K) *ᵥ v), ← hP ((P⁻¹ : GL ι K) *ᵥ v)]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]

theorem projImage_map_conj {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (H : Subgroup (GL ι K)) (P : GL ι K) :
    projImage (H.map (MulAut.conj P).toMonoidHom) =
      (projImage H).map (MulAut.conj (ProjGenLinGroup.mk P)).toMonoidHom := by
  have h : ProjGenLinGroup.mk.comp (MulAut.conj P).toMonoidHom =
      (MulAut.conj (ProjGenLinGroup.mk P)).toMonoidHom.comp ProjGenLinGroup.mk := by
    ext A
    change ProjGenLinGroup.mk (P * A * P⁻¹) =
      MulAut.conj (ProjGenLinGroup.mk P) (ProjGenLinGroup.mk A)
    rw [MulAut.conj_apply]
    simp only [map_mul, map_inv]
  unfold projImage
  rw [Subgroup.map_map, Subgroup.map_map, h]

end CFSG.PGLModel
