module

public import CFSG.LieType.AlgebraicGroups.MatrixFixedPoints
public import CFSG.LieType.AlgebraicGroups.ReductiveFixedComponentsThree
public import CFSG.LieType.AlgebraicGroups.FixedComponentSmooth
public import CFSG.Open.LocalVocabulary

public noncomputable section

open WithConv
open scoped CFSG.ConvolutionPoints
namespace CFSG.LieType.AlgebraicGroups
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
variable {τ : Tag} {k : Type} [Field k] [IsAlgClosed k]

theorem matrixFixedCoordinatePointMap_data (M : Subgroup (ModGL τ k))
    (hM : IsPointClosed k (transportPoints (modGLPoint τ k) (M : Set (ModGL τ k))))
    (a : ModGL τ k) (ha : ∀ y ∈ M, a * y * a⁻¹ ∈ M)
    [Algebra.Smooth k (MatrixComponents.coordinateHopf M)]
    (h3 : (3 : k) ≠ 0) (ha3 : a ^ 3 = 1) :
    ∃ θ : MatrixComponents.coordinateHopf (M ⊓ Subgroup.centralizer {a}) →ₐc[k]
        fixedCoordinate (MatrixComponents.coordinateHopf M) (matrixInnerCoordinate M a ha),
      ∀ x : TauCeti.HopfAlgebra.points (R := k)
        (H := fixedCoordinate (MatrixComponents.coordinateHopf M) (matrixInnerCoordinate M a ha))
        (CommAlgCat.of k k),
        MatrixComponents.coordinatePointsMulEquiv (M ⊓ Subgroup.centralizer {a})
          (isPointClosed_inf hM (isPointClosed_centralizer {a}))
          (TauCeti.AlgHom.mapDomain θ x) = matrixFixedPointsHom M hM a ha x := by
  let F := fixedCoordinate (MatrixComponents.coordinateHopf M) (matrixInnerCoordinate M a ha)
  let N := M ⊓ Subgroup.centralizer {a}
  let e := modGLPoint τ k
  let I := subgroupIdeal (N.map e.toMonoidHom)
  let qF := (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient (MatrixComponents.coordinateHopf M)
    (fixedHopfIdeal (MatrixComponents.coordinateHopf M) (matrixInnerCoordinate M a ha))).hom.hom
  let πb : GLCoord k (Label τ) →ₐc[k] MatrixComponents.coordinateHopf M :=
    Bialgebra.Quotient.mkBialgHom (subgroupIdeal (M.map e.toMonoidHom))
  let fB : GLCoord k (Label τ) →ₐc[k] F := qF.comp πb
  let : Algebra.Smooth k F := smooth_fixedCoordinate_three (MatrixComponents.coordinateHopf M)
    h3 (matrixInnerCoordinate M a ha) (matrixInnerCoordinate_cube M a ha ha3)
  let : IsReduced F := TauCeti.isReduced_of_smooth k F
  have hf : ∀ z : F →ₐ[k] k, z.comp fB.toAlgHom ∈ transportPoints e (N : Set (ModGL τ k)) := by
    intro z
    refine ⟨matrixFixedPointsHom M hM a ha (toConv z),
      (matrixFixedPointsHom M hM a ha (toConv z)).property, ?_⟩
    change (e (matrixFixedPointsHom M hM a ha (toConv z) : ModGL τ k)).ofConv = _
    dsimp only [e]
    rw [matrixFixedPointsHom_apply, MatrixComponents.coordinatePointsMulEquiv_coe,
      MulEquiv.apply_symm_apply, ofConv_toConv]
    rfl
  have hkill : ∀ b ∈ I, fB b = 0 := by
    intro b hb
    exact map_eq_zero_of_comp_mem (transportPoints e (N : Set (ModGL τ k))) fB.toAlgHom hf
      (by simpa only [I, subgroupIdeal, subgroupPoints_map] using hb)
  let θ := bialgHomQuotientLift I fB hkill
  refine ⟨θ, fun x => ?_⟩
  apply Subtype.ext
  rw [MatrixComponents.coordinatePointsMulEquiv_coe, matrixFixedPointsHom_apply,
    MatrixComponents.coordinatePointsMulEquiv_coe]
  apply congrArg e.symm
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro b
  change x.ofConv (θ (Ideal.Quotient.mk I b)) = x.ofConv (fB b)
  rw [bialgHomQuotientLift_mk]

end CFSG.LieType.AlgebraicGroups
