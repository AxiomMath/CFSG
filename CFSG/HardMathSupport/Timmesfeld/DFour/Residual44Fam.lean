module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LS8Fam
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaThreeFamily

public section

namespace CFSG.HardMathSupport.Timmesfeld.DFour

open Module CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit
open CFSG.ComponentClassification.HarrisLit.T1.S8
open CFSG.ComponentClassification.UnbalancedCatalog.ThreeFamily
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

variable {K : Type} [Field K]

theorem exists_maximal_family_mem [Finite K] {Y : Submodule K (Fin (2 * 4) → K)}
    (hY4 : finrank K Y = 4) (hYs : ∀ v ∈ Y, coordinateQuadPlus 4 K v = 0) :
    ∃ U ∈ plusCX 4 K ∪ plusCXstar 4 K (by norm_num),
      ∀ A : matrixDerived (coordinateQuadPlus 4 K),
        Y.map (matrixLinearEquiv A.val).toLinearMap = Y →
          matrixProjectiveProjection (coordinateQuadPlus 4 K) A ∈ U := by
  set R := reindexVectorEquiv (K := K) (plusIndexEquiv 4) with hR
  have hRQ : ∀ x, coordinateQuadPlus 4 K (R x) = quadPlus 4 K x :=
    reindexQuadraticForm_map (plusIndexEquiv 4) (quadPlus 4 K)
  set Ys := Y.map R.symm.toLinearMap with hYsdef
  have hYsing : Ys ∈ singularSubspaces (quadPlus 4 K) 4 := by
    refine ⟨by rw [hYsdef, LinearEquiv.finrank_map_eq, hY4], ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    rw [← hRQ, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact hYs v hv
  have hstab : ∀ A : matrixDerived (coordinateQuadPlus 4 K),
      Y.map (matrixLinearEquiv A.val).toLinearMap = Y →
        matrixProjectiveProjection (coordinateQuadPlus 4 K) A ∈
          (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) Ys).map
            (plusCoordinateEquiv 4 K).toMonoidHom := by
    intro A hA
    refine ⟨QuotientGroup.mk' _ ((Rd8 K).symm A), ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_statedProjectiveSubspaceStabilizer_mk,
        mem_statedDerivedSubspaceStabilizer]
      have hcomp : (toLinEquiv _ K ((Rd8 K).symm A).val).toLinearMap.comp R.symm.toLinearMap =
          R.symm.toLinearMap.comp (matrixLinearEquiv A.val).toLinearMap := by
        refine LinearMap.ext fun x => ?_
        exact statedDerivedReindexEquiv_symm_vector (plusIndexEquiv 4) (quadPlus 4 K)
          (coe_quadPlus 4 K) A x
      rw [hYsdef, ← Submodule.map_comp, hcomp, Submodule.map_comp, hA]
    · change plusCoordinateEquiv 4 K (QuotientGroup.mk' _ ((Rd8 K).symm A)) = _
      rw [← plusCoordinateEquiv_symm_mk, MulEquiv.apply_symm_apply]
  obtain ⟨-, -, -, -, hcover, -⟩ :=
    orthogonal_geometry_split_maximal_family_orbits (K := K) (r := 4) (by norm_num)
  refine ⟨_, ?_, hstab⟩
  rcases hcover Ys hYsing with hX | hX
  · left
    rw [plusCX, ← familyTransport_conjugacy, familyTransport_apply,
      conjugacyFamily_eq_image (by norm_num)]
    exact ⟨_, ⟨Ys, hX, rfl⟩, rfl⟩
  · right
    rw [plusCXstar, ← familyTransport_conjugacy, familyTransport_apply,
      conjugacyFamily_eq_image (by norm_num)]
    exact ⟨_, ⟨Ys, hX, rfl⟩, rfl⟩

end CFSG.HardMathSupport.Timmesfeld.DFour
