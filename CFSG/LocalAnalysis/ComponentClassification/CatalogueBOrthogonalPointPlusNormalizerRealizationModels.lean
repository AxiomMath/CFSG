module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusNormalizerRealizationBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointModelNormalizerBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointSemilinearRealizationSimilarity
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryRealization

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusNormalizerRealization

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CatalogueBOrthogonalPointAction (Points PointPerp)
open CatalogueBOrthogonalPointData CatalogueBOrthogonalPointIsometry

universe u

theorem coordinate_polar_perm_mem_similarityPointImage
    {K : Type u} [Field K] {n : ℕ} (hn : 3 ≤ n)
    (phi : Equiv.Perm (Points (coordinateQuadPlus n K)))
    (hphi : ∀ L M, PointPerp (phi L) (phi M) ↔ PointPerp L M) :
    phi ∈ similarityPointImage (coordinateQuadPlus n K) := by
  let eP := pointIsometryEquiv (coordinatePlusIsometry n K)
  let psi : Equiv.Perm (Points (quadPlus n K)) := (eP.trans phi).trans eP.symm
  have hpsi : ∀ L M : Points (quadPlus n K),
      PolarOrtho (quadPlus n K) L.val M.val ↔
        PolarOrtho (quadPlus n K) (psi L).val (psi M).val := by
    intro L M
    change PointPerp L M ↔ PointPerp (eP.symm (phi (eP L))) (eP.symm (phi (eP M)))
    exact (pointPerp_isometry_iff (coordinatePlusIsometry n K) L M).symm.trans
      ((hphi (eP L) (eP M)).symm.trans
        (pointPerp_isometry_symm_iff (coordinatePlusIsometry n K)
          (phi (eP L)) (phi (eP M))).symm)
  obtain ⟨A, sigma, mu, hmu, hA, himages⟩ :=
    orthogonal_geometry_split_polar_realization hn psi hpsi
  let muUnit : Kˣ := Units.mk0 mu hmu
  have hunit : ∀ v, quadPlus n K (A (sCoord sigma v)) =
      (muUnit : K) * sigma (quadPlus n K v) := hA
  apply CatalogueBOrthogonalPointSemilinearRealization.pointPerm_mem_similarityPointImage
    (coordinateQuadPlus n K) sigma (coordinateSemilinear A sigma) muUnit
    (coordinateSemilinear_similarity A sigma muUnit hunit) phi
  exact coordinate_point_image_of_split_realization A sigma phi himages

theorem coordinate_normalizer_eq_of_geometry
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n)
    (hQ : (coordinateQuadPlus n K).polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧
      ∀ x ∈ T, coordinateQuadPlus n K x = 0)
    (ha : CatalogueBOrthogonalPointAction.ActionProperties (coordinateQuadPlus n K)
      (projectivePointAction (coordinateQuadPlus n K))) :
    projectivePointNormalizer (coordinateQuadPlus n K) =
      similarityPointImage (coordinateQuadPlus n K) := by
  apply le_antisymm
  · intro phi hphi
    have hperp := CatalogueBOrthogonalPointModelNormalizer.action_normalizer_orthogonality
      (coordinateQuadPlus n K) (projectivePointAction (coordinateQuadPlus n K))
      hQ hT ha phi hphi
    exact coordinate_polar_perm_mem_similarityPointImage hn phi hperp.1
  · exact similarityPointImage_le_normalizer (coordinateQuadPlus n K)

theorem coordinate_plus_normalizer_eq
    (n : ℕ) (K : Type) [Field K] [Finite K] (hn : 3 ≤ n) :
    projectivePointNormalizer (coordinateQuadPlus n K) =
      similarityPointImage (coordinateQuadPlus n K) := by
  have hreg := regular_coordinateQuadPlus n K hn
  exact coordinate_normalizer_eq_of_geometry hn hreg.1 hreg.2
    (coordinate_plus_point_action_properties n K hn)

theorem model_plus_projective_normalizer_eq
    {H : Type} [Group H] {n p f : ℕ}
    (h : StatedClassicalModel H .POmegaPlus n p f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = p ^ f)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) :
    projectivePointNormalizer (coordinateQuadPlus n K) =
      similarityPointImage (coordinateQuadPlus n K) := by
  have hn : 3 ≤ n := by have := h.1.2.2; omega
  obtain ⟨_, hQ, hT, _, ha, _⟩ := coordinate_model_witness_plus h K hK e
  exact coordinate_normalizer_eq_of_geometry hn hQ hT ha

theorem model_plus_witness_action_normalizer_eq
    {H : Type} [Group H] {n p f : ℕ}
    (h : StatedClassicalModel H .POmegaPlus n p f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = p ^ f)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) :
    Subgroup.normalizer
        (((projectivePointAction (coordinateQuadPlus n K)).comp
          (coordinatePlusWitnessEquiv K e).toMonoidHom).range :
            Set (Equiv.Perm (Points (coordinateQuadPlus n K)))) =
      similarityPointImage (coordinateQuadPlus n K) := by
  rw [CatalogueBOrthogonalPointModelNormalizer.action_normalizer_comp_equiv
    (coordinateQuadPlus n K) (projectivePointAction (coordinateQuadPlus n K))
    (coordinatePlusWitnessEquiv K e)]
  exact model_plus_projective_normalizer_eq h K hK e

theorem orthogonal_geometry_plus_normalizer_realization
    {H : Type} [Group H] {n p f : ℕ}
    (h : StatedClassicalModel H .POmegaPlus n p f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = p ^ f)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) :
    projectivePointNormalizer (coordinateQuadPlus n K) =
        similarityPointImage (coordinateQuadPlus n K) ∧
      Subgroup.normalizer
          (((projectivePointAction (coordinateQuadPlus n K)).comp
            (coordinatePlusWitnessEquiv K e).toMonoidHom).range :
              Set (Equiv.Perm (Points (coordinateQuadPlus n K)))) =
        similarityPointImage (coordinateQuadPlus n K) :=
  ⟨model_plus_projective_normalizer_eq h K hK e,
    model_plus_witness_action_normalizer_eq h K hK e⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusNormalizerRealization
