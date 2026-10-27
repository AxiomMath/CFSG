module

public import CFSG.LieType.AlgebraicGroups.FixedComponentSmooth
public import TauCeti.Algebra.AlgebraicGroup.Torus.Characterization
public import TauCeti.Algebra.AlgebraicGroup.Torus.Reductive
public import TauCeti.Algebra.AlgebraicGroup.Smooth.IdentityComponent
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.ClosedSubgroup

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CategoryTheory

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

theorem torus_identityComponent_fixedCoordinate_three
    (T : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (hT : TauCeti.torusCommHopfAlgProperty k T)
    (h3 : (3 : k) ≠ 0) (σ : T →ₐc[k] T) (hσ : (σ.comp σ).comp σ = BialgHom.id k T) :
    TauCeti.torusCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.identityComponent (fixedCoordinate T σ)) := by
  set q : T ⟶ fixedCoordinate T σ :=
    TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient T (fixedHopfIdeal T σ)
  set r : fixedCoordinate T σ ⟶
      TauCeti.FiniteTypeCommHopfAlgCat.identityComponent (fixedCoordinate T σ) :=
    TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient (fixedCoordinate T σ)
      (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k)
        (H := fixedCoordinate T σ))
  have hq : Function.Surjective (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom q) := by
    rw [show TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom q =
      (TauCeti.CommHopfAlgCat.mkQuotient T.obj (fixedHopfIdeal T σ)).hom from rfl]
    exact TauCeti.CommHopfAlgCat.mkQuotient_surjective T.obj (fixedHopfIdeal T σ)
  have hr : Function.Surjective (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom r) := by
    rw [show TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom r =
      (TauCeti.CommHopfAlgCat.mkQuotient (fixedCoordinate T σ).obj
        (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k)
          (H := fixedCoordinate T σ))).hom from rfl]
    exact TauCeti.CommHopfAlgCat.mkQuotient_surjective _ _
  have hqr : Function.Surjective
      (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom (q ≫ r)) := by
    rw [TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom_comp]
    exact hr.comp hq
  rw [TauCeti.torusCommHopfAlgProperty.iff_multiplicativeType_and_geometricallyConnected_and_geometricallyReduced]
  refine ⟨?_, ?_, ?_⟩
  · have hmt : TauCeti.multiplicativeTypeCommHopfAlgProperty k T :=
      hT.multiplicativeType k T
    rw [TauCeti.multiplicativeTypeCommHopfAlgProperty_iff] at hmt ⊢
    exact TauCeti.DiagonalizableGroup.groupLikeSpannedProperty.of_surjective
      (AlgebraicClosure k)
      (TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) T)
      (TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k)
        (TauCeti.FiniteTypeCommHopfAlgCat.identityComponent (fixedCoordinate T σ)))
      (TauCeti.FiniteTypeCommHopfAlgCat.baseChangeMap (K := AlgebraicClosure k) (q ≫ r))
      (by
        rw [TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom_baseChangeMap]
        exact TauCeti.CommHopfAlgCat.baseChangeMap_surjective
          (K := AlgebraicClosure k) (q ≫ r).hom hqr) hmt
  · exact TauCeti.FiniteTypeCommHopfAlgCat.geometricallyConnected_identityComponent
      (fixedCoordinate T σ)
  · have hTsmooth : Algebra.Smooth k T :=
      (TauCeti.smoothCommHopfAlgProperty_iff T.obj).mp (hT.smooth k T)
    have hfsmooth : Algebra.Smooth k (fixedCoordinate T σ) :=
      smooth_fixedCoordinate_three T h3 σ hσ
    have hXsmooth : Algebra.Smooth k
        (TauCeti.FiniteTypeCommHopfAlgCat.identityComponent (fixedCoordinate T σ)) :=
      TauCeti.FiniteTypeCommHopfAlgCat.smooth_identityComponent (fixedCoordinate T σ)
    exact TauCeti.geometricallyReducedCommHopfAlgProperty_of_smooth k
      (TauCeti.FiniteTypeCommHopfAlgCat.identityComponent (fixedCoordinate T σ)).obj
      ((TauCeti.smoothCommHopfAlgProperty_iff _).mpr hXsmooth)

theorem reductive_identityComponent_fixedCoordinate_torus_three
    (T : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (hT : TauCeti.torusCommHopfAlgProperty k T)
    (h3 : (3 : k) ≠ 0) (σ : T →ₐc[k] T) (hσ : (σ.comp σ).comp σ = BialgHom.id k T) :
    TauCeti.reductiveCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.identityComponent (fixedCoordinate T σ)) :=
  (torus_identityComponent_fixedCoordinate_three T hT h3 σ hσ).reductive

end CFSG.LieType.AlgebraicGroups
