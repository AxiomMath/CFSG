module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataConjugation

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

open Matrix

universe u

variable {K : Type u} [Field K] {d : ℕ}

@[expose] def matrixDerived (Q : QuadraticForm K (Fin d → K)) :
    Subgroup (GL (Fin d) K) := ⁅matrixIsometries Q, matrixIsometries Q⁆

theorem matrixDerived_le_isometries (Q : QuadraticForm K (Fin d → K)) :
    matrixDerived Q ≤ matrixIsometries Q := Subgroup.commutator_le_self _

theorem matrixDerived_eq_map_commutator (Q : QuadraticForm K (Fin d → K)) :
    matrixDerived Q = (commutator (matrixIsometries Q)).map (matrixIsometries Q).subtype :=
  (Subgroup.map_subtype_commutator _).symm

theorem matrixScalars_eq_center : matrixScalars d K = Subgroup.center (GL (Fin d) K) :=
  (GeneralLinearGroup.center_eq_range_scalar).symm

instance matrixScalars_normal : (matrixScalars d K).Normal := by
  rw [matrixScalars_eq_center]
  infer_instance

@[expose] def matrixDerivedScalars (Q : QuadraticForm K (Fin d → K)) :
    Subgroup (matrixDerived Q) := (matrixScalars d K).subgroupOf (matrixDerived Q)

theorem mem_matrixDerivedScalars_iff (Q : QuadraticForm K (Fin d → K))
    (A : matrixDerived Q) :
    A ∈ matrixDerivedScalars Q ↔ ∃ c : Kˣ,
      GeneralLinearGroup.scalar (Fin d) c = A.val := Iff.rfl

theorem matrixDerivedScalars_le_center (Q : QuadraticForm K (Fin d → K)) :
    matrixDerivedScalars Q ≤ Subgroup.center (matrixDerived Q) := by
  intro A hA
  apply Subgroup.mem_center_iff.mpr
  intro B
  apply Subtype.ext
  have hcentral : A.val ∈ Subgroup.center (GL (Fin d) K) :=
    matrixScalars_eq_center.le hA
  exact Subgroup.mem_center_iff.mp hcentral B.val

instance matrixDerivedScalars_normal (Q : QuadraticForm K (Fin d → K)) :
    (matrixDerivedScalars Q).Normal :=
  Subgroup.normal_of_le_center (matrixDerivedScalars_le_center Q)

abbrev matrixProjectiveDerived (Q : QuadraticForm K (Fin d → K)) :=
  matrixDerived Q ⧸ matrixDerivedScalars Q

@[expose] def matrixProjectiveProjection (Q : QuadraticForm K (Fin d → K)) :
    matrixDerived Q →* matrixProjectiveDerived Q := QuotientGroup.mk' _

theorem matrixProjectiveProjection_surjective (Q : QuadraticForm K (Fin d → K)) :
    Function.Surjective (matrixProjectiveProjection Q) := QuotientGroup.mk'_surjective _

theorem matrixDerived_invariant (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) :
    (matrixDerived Q).map (matrixConjugation g.val).toMonoidHom = matrixDerived Q := by
  rw [matrixDerived, Subgroup.map_commutator, matrixIsometries_invariant]

@[expose] def matrixDerivedConjugation (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) : MulAut (matrixDerived Q) :=
  ((matrixConjugation g.val).subgroupMap (matrixDerived Q)).trans
    (MulEquiv.subgroupCongr (matrixDerived_invariant Q g))

theorem matrixDerivedConjugation_val (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) (A : matrixDerived Q) :
    (matrixDerivedConjugation Q g A).val =
      g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K g.val.right A.val *
        g.val.left⁻¹ := rfl

theorem matrixDerivedScalars_invariant (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) :
    (matrixDerivedScalars Q).map (matrixDerivedConjugation Q g).toMonoidHom =
      matrixDerivedScalars Q := by
  have hS := matrixScalars_invariant g.val
  have hSinv : (matrixScalars d K).map (matrixConjugation g.val).symm.toMonoidHom =
      matrixScalars d K :=
    (Subgroup.map_symm_eq_iff_map_eq (matrixScalars d K)
      (H := matrixScalars d K) (e := matrixConjugation g.val)).mpr hS
  ext A
  constructor
  · rintro ⟨B, hB, rfl⟩
    change matrixConjugation g.val B.val ∈ matrixScalars d K
    rw [← hS]
    exact Subgroup.mem_map_of_mem (matrixConjugation g.val).toMonoidHom hB
  · intro hA
    refine ⟨(matrixDerivedConjugation Q g).symm A, ?_, by simp⟩
    have hval : ((matrixDerivedConjugation Q g).symm A).val =
        (matrixConjugation g.val).symm A.val := by
      apply (matrixConjugation g.val).injective
      rw [MulEquiv.apply_symm_apply]
      exact congrArg Subtype.val ((matrixDerivedConjugation Q g).apply_symm_apply A)
    change ((matrixDerivedConjugation Q g).symm A).val ∈ matrixScalars d K
    rw [hval, ← hSinv]
    exact Subgroup.mem_map_of_mem (matrixConjugation g.val).symm.toMonoidHom hA

@[expose] def matrixProjectiveConjugation (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) : MulAut (matrixProjectiveDerived Q) :=
  QuotientGroup.congr (matrixDerivedScalars Q) (matrixDerivedScalars Q)
    (matrixDerivedConjugation Q g) (matrixDerivedScalars_invariant Q g)

theorem matrixProjectiveConjugation_mk (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) (A : matrixDerived Q) :
    matrixProjectiveConjugation Q g (matrixProjectiveProjection Q A) =
      matrixProjectiveProjection Q (matrixDerivedConjugation Q g A) :=
  QuotientGroup.congr_mk' _ _ _ _ A

theorem matrixDerivedConjugation_mul (Q : QuadraticForm K (Fin d → K))
    (g h : similarityPairs Q) (A : matrixDerived Q) :
    matrixDerivedConjugation Q (g * h) A =
      matrixDerivedConjugation Q g (matrixDerivedConjugation Q h A) := by
  apply Subtype.ext
  change matrixConjugationHom (g.val * h.val) A.val =
    matrixConjugationHom g.val (matrixConjugationHom h.val A.val)
  rw [map_mul]
  rfl

theorem matrixDerivedConjugation_one (Q : QuadraticForm K (Fin d → K))
    (A : matrixDerived Q) : matrixDerivedConjugation Q 1 A = A := by
  apply Subtype.ext
  change matrixConjugationHom 1 A.val = A.val
  rw [map_one]
  rfl

@[expose] def matrixProjectiveConjugationHom (Q : QuadraticForm K (Fin d → K)) :
    similarityPairs Q →* MulAut (matrixProjectiveDerived Q) where
  toFun := matrixProjectiveConjugation Q
  map_one' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective Q x
    rw [matrixProjectiveConjugation_mk, matrixDerivedConjugation_one]
    rfl
  map_mul' g h := by
    apply MulEquiv.ext
    intro x
    obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective Q x
    change matrixProjectiveConjugation Q (g * h) (matrixProjectiveProjection Q A) =
      matrixProjectiveConjugation Q g
        (matrixProjectiveConjugation Q h (matrixProjectiveProjection Q A))
    rw [matrixProjectiveConjugation_mk, matrixProjectiveConjugation_mk,
      matrixProjectiveConjugation_mk, matrixDerivedConjugation_mul]

@[expose] def matrixProjectiveImage (Q : QuadraticForm K (Fin d → K)) :
    Subgroup (MulAut (matrixProjectiveDerived Q)) := (matrixProjectiveConjugationHom Q).range

theorem mem_matrixProjectiveImage_iff (Q : QuadraticForm K (Fin d → K))
    (alpha : MulAut (matrixProjectiveDerived Q)) :
    alpha ∈ matrixProjectiveImage Q ↔
      ∃ g : similarityPairs Q, matrixProjectiveConjugation Q g = alpha := Iff.rfl

end CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
