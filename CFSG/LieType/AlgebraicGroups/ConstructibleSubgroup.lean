module

public import CFSG.LieType.AlgebraicGroups.ConstructibleSubgroupGL
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open TensorProduct WithConv
open scoped CFSG.ConvolutionPoints

theorem exceptional_Lang_constructible_subgroup_closed (k : Type) [Field k] [IsAlgClosed k] :
    (∀ (A : Type) [CommRing A] [HopfAlgebra k A] [Algebra.FiniteType k A]
      (H : Subgroup (WithConv (A →ₐ[k] k))),
      IsPointConstructible k (subgroupPoints H) → IsPointIrreducible k (subgroupPoints H) →
        IsConnectedAlgebraicSubgroup k H) ∧
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H : Subgroup (Matrix.GeneralLinearGroup ι k)),
      IsPointConstructible k (glPoints (H : Set (Matrix.GeneralLinearGroup ι k))) →
      IsPointIrreducible k (glPoints (H : Set (Matrix.GeneralLinearGroup ι k))) →
        IsPointClosed k (glPoints (H : Set (Matrix.GeneralLinearGroup ι k))) ∧
        IsConnectedAlgebraicSubgroup k (glPointSubgroup H) ∧
        ∃ e : WithConv ((GLCoord k ι ⧸ subgroupIdeal (glPointSubgroup H)) →ₐ[k] k) ≃* H, ∀ φ,
          ((e φ : H) : Matrix.GeneralLinearGroup ι k) =
            glPointEquiv.symm (toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ k _)))) ∧
    (∀ (r : ℕ) (ι : Fin r → Type) [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
      (H : Subgroup (∀ i, Matrix.GeneralLinearGroup (ι i) k)),
      IsPointConstructible k (transportPoints (glProdPointEquiv k r ι) H) →
      IsPointIrreducible k (transportPoints (glProdPointEquiv k r ι) H) →
        IsPointClosed k (transportPoints (glProdPointEquiv k r ι) H) ∧
        IsConnectedAlgebraicSubgroup k (H.map (glProdPointEquiv k r ι).toMonoidHom) ∧
        ∃ e : WithConv (((glProdCoord k r ι).carrier ⧸
            subgroupIdeal (H.map (glProdPointEquiv k r ι).toMonoidHom)) →ₐ[k] k) ≃* H, ∀ φ,
          ((e φ : H) : ∀ i, Matrix.GeneralLinearGroup (ι i) k) =
            (glProdPointEquiv k r ι).symm (toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ k _)))) ∧
    ∀ (ι₁ ι₂ : Type) [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
      (H : Subgroup (Matrix.GeneralLinearGroup ι₁ k × Matrix.GeneralLinearGroup ι₂ k)),
      IsPointConstructible k
          (glPairPoints (H : Set (Matrix.GeneralLinearGroup ι₁ k ×
            Matrix.GeneralLinearGroup ι₂ k))) →
      IsPointIrreducible k
          (glPairPoints (H : Set (Matrix.GeneralLinearGroup ι₁ k ×
            Matrix.GeneralLinearGroup ι₂ k))) →
        IsPointClosed k
          (glPairPoints (H : Set (Matrix.GeneralLinearGroup ι₁ k ×
            Matrix.GeneralLinearGroup ι₂ k))) ∧
        IsConnectedAlgebraicSubgroup k (glPairPointSubgroup H) ∧
        ∃ e : WithConv ((GLCoord k ι₁ ⊗[k] GLCoord k ι₂ ⧸
            subgroupIdeal (glPairPointSubgroup H)) →ₐ[k] k) ≃* H, ∀ φ,
          ((e φ : H) : Matrix.GeneralLinearGroup ι₁ k × Matrix.GeneralLinearGroup ι₂ k) =
            glPairPointEquiv.symm (toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ k _))) :=
  ⟨fun _ _ _ _ H hcons hirr => isConnectedAlgebraicSubgroup H hcons hirr,
    fun _ _ _ H hcons hirr => isConnectedAlgebraicSubgroup_map glPointEquiv H hcons hirr,
    fun r ι _ _ H hcons hirr =>
      isConnectedAlgebraicSubgroup_map (glProdPointEquiv k r ι) H hcons hirr,
    fun _ _ _ _ _ _ H hcons hirr =>
      isConnectedAlgebraicSubgroup_map glPairPointEquiv H hcons hirr⟩

end CFSG.LieType.AlgebraicGroups
