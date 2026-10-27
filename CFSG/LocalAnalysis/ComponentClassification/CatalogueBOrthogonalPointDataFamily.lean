module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBStabilizerFamilyTransport
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointData

open CatalogueBOrthogonalSemilinear CatalogueBOrthogonalPointAction
open CatalogueBStabilizerFamily

universe u

variable {K : Type u} [Field K] {d : ℕ}

theorem similarity_projective_covariance (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) (x : matrixProjectiveDerived Q) :
    similarityPointAction Q g * projectivePointAction Q x *
        (similarityPointAction Q g)⁻¹ =
      projectivePointAction Q (matrixProjectiveConjugationHom Q g x) := by
  obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective Q x
  change _ = projectivePointAction Q
    (matrixProjectiveConjugation Q g (matrixProjectiveProjection Q A))
  rw [matrixProjectiveConjugation_mk, projectivePointAction_mk,
    projectivePointAction_mk]
  change similarityPointAction Q g * similarityPointAction Q (matrixDerivedInclusion Q A) *
    (similarityPointAction Q g)⁻¹ =
    similarityPointAction Q (matrixDerivedInclusion Q (matrixDerivedConjugation Q g A))
  rw [matrixDerivedInclusion_conjugation, map_mul, map_mul, map_inv]

@[expose] def projectivePointStabilizer (Q : QuadraticForm K (Fin d → K))
    (L : Points Q) : Subgroup (matrixProjectiveDerived Q) :=
  pointStabilizer (projectivePointAction Q) L

theorem mem_projectivePointStabilizer_iff (Q : QuadraticForm K (Fin d → K))
    (L : Points Q) (x : matrixProjectiveDerived Q) :
    x ∈ projectivePointStabilizer Q L ↔ projectivePointAction Q x L = L := Iff.rfl

@[expose] def projectivePointFamily (Q : QuadraticForm K (Fin d → K)) :
    Set (Subgroup (matrixProjectiveDerived Q)) := family (projectivePointAction Q)

@[expose] def projectivePointFamilyAut (Q : QuadraticForm K (Fin d → K)) :
    Subgroup (MulAut (matrixProjectiveDerived Q)) := familyAut (projectivePointAction Q)

theorem mem_projectivePointFamilyAut_iff (Q : QuadraticForm K (Fin d → K))
    (alpha : MulAut (matrixProjectiveDerived Q)) :
    alpha ∈ projectivePointFamilyAut Q ↔
      (fun U => U.map alpha.toMonoidHom) '' projectivePointFamily Q =
        projectivePointFamily Q := Iff.rfl

theorem similarity_projective_stabilizer (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) (L : Points Q) :
    (projectivePointStabilizer Q L).map
        (matrixProjectiveConjugationHom Q g).toMonoidHom =
      projectivePointStabilizer Q (similarityPointAction Q g L) :=
  covariance_stabilizer (projectivePointAction Q) (matrixProjectiveConjugationHom Q g)
    (similarityPointAction Q g) (similarity_projective_covariance Q g) L

theorem projective_inner_le_pointFamilyAut (Q : QuadraticForm K (Fin d → K)) :
    OuterAutomorphisms.inner (matrixProjectiveDerived Q) ≤ projectivePointFamilyAut Q :=
  inner_le_familyAut (projectivePointAction Q)

theorem projective_image_le_pointFamilyAut (Q : QuadraticForm K (Fin d → K)) :
    matrixProjectiveImage Q ≤ projectivePointFamilyAut Q :=
  compatible_aut_range (projectivePointAction Q) (matrixProjectiveConjugationHom Q)
    (similarityPointAction Q) (similarity_projective_covariance Q)

@[expose] def similarityPointImage (Q : QuadraticForm K (Fin d → K)) :
    Subgroup (Equiv.Perm (Points Q)) := (similarityPointAction Q).range

theorem projective_image_le_similarityPointImage (Q : QuadraticForm K (Fin d → K)) :
    (projectivePointAction Q).range ≤ similarityPointImage Q :=
  projectivePointAction_range_le_similarity Q

theorem similarityPointImage_le_normalizer (Q : QuadraticForm K (Fin d → K)) :
    similarityPointImage Q ≤
      Subgroup.normalizer ((projectivePointAction Q).range : Set (Equiv.Perm (Points Q))) :=
  compatible_perm_range (projectivePointAction Q) (matrixProjectiveConjugationHom Q)
    (similarityPointAction Q) (similarity_projective_covariance Q)

theorem orthogonal_geometry_point_data (hd : 1 ≤ d)
    (Q : QuadraticForm K (Fin d → K)) (hQ : Q ≠ 0) :
    OuterAutomorphisms.inner (matrixProjectiveDerived Q) ≤ projectivePointFamilyAut Q ∧
    matrixProjectiveImage Q ≤ projectivePointFamilyAut Q ∧
    (projectivePointAction Q).range ≤ similarityPointImage Q ∧
    similarityPointImage Q ≤
      Subgroup.normalizer ((projectivePointAction Q).range : Set (Equiv.Perm (Points Q))) := by
  have _hd := hd
  have _hQ := hQ
  exact ⟨projective_inner_le_pointFamilyAut Q, projective_image_le_pointFamilyAut Q,
    projective_image_le_similarityPointImage Q, similarityPointImage_le_normalizer Q⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalPointData
