module

public import CFSG.LieType.AlgebraicGroups.ConstructibleSubgroupClosed
public import CFSG.LieType.AlgebraicGroups.HopfTensorPoints
public import CFSG.LieType.AlgebraicGroups.GLCoordPoints
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open TensorProduct WithConv
open scoped CFSG.ConvolutionPoints

variable {k : Type} [Field k]

section Transport

variable {A : Type} [CommRing A] [HopfAlgebra k A] {G : Type} [Group G]

abbrev transportPoints (E : G ≃* WithConv (A →ₐ[k] k)) (S : Set G) : Set (A →ₐ[k] k) :=
  (fun g => (E g).ofConv) '' S

theorem subgroupPoints_map (E : G ≃* WithConv (A →ₐ[k] k)) (H : Subgroup G) :
    subgroupPoints (H.map E.toMonoidHom) = transportPoints E H := by
  ext y
  constructor
  · rintro ⟨g, hg, hgy⟩
    exact ⟨g, hg, congrArg ofConv hgy⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩

variable [IsAlgClosed k] [Algebra.FiniteType k A]

theorem isConnectedAlgebraicSubgroup_map (E : G ≃* WithConv (A →ₐ[k] k)) (H : Subgroup G)
    (hcons : IsPointConstructible k (transportPoints E H))
    (hirr : IsPointIrreducible k (transportPoints E H)) :
    IsPointClosed k (transportPoints E H) ∧ IsConnectedAlgebraicSubgroup k (H.map E.toMonoidHom) ∧
      ∃ e : WithConv ((A ⧸ subgroupIdeal (H.map E.toMonoidHom)) →ₐ[k] k) ≃* H, ∀ φ,
        ((e φ : H) : G) = E.symm (toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ k _))) := by
  rw [← subgroupPoints_map] at hcons hirr ⊢
  have h := isConnectedAlgebraicSubgroup (H.map E.toMonoidHom) hcons hirr
  exact ⟨h.isPointClosed, h, (subgroupQuotientPointsEquiv _ h.pointsZero_eq).trans
    (E.subgroupMap H).symm, fun _ => rfl⟩

end Transport

section GeneralLinear

variable {ι : Type} [Fintype ι] [DecidableEq ι]

abbrev glPoints (S : Set (Matrix.GeneralLinearGroup ι k)) : Set (GLCoord k ι →ₐ[k] k) :=
  transportPoints glPointEquiv S

abbrev glPointSubgroup (H : Subgroup (Matrix.GeneralLinearGroup ι k)) :
    Subgroup (WithConv (GLCoord k ι →ₐ[k] k)) :=
  H.map glPointEquiv.toMonoidHom

end GeneralLinear

section Pair

variable {ι₁ ι₂ : Type} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]

@[expose] def glPairPointEquiv :
    Matrix.GeneralLinearGroup ι₁ k × Matrix.GeneralLinearGroup ι₂ k ≃*
      WithConv (GLCoord k ι₁ ⊗[k] GLCoord k ι₂ →ₐ[k] k) :=
  (glPointEquiv.prodCongr glPointEquiv).trans tensorPointMulEquiv.symm

theorem glPairPointEquiv_apply
    (p : Matrix.GeneralLinearGroup ι₁ k × Matrix.GeneralLinearGroup ι₂ k) :
    (glPairPointEquiv p).ofConv =
      tensorPointEquiv ((glPointEquiv p.1).ofConv, (glPointEquiv p.2).ofConv) :=
  rfl

abbrev glPairPoints (S : Set (Matrix.GeneralLinearGroup ι₁ k × Matrix.GeneralLinearGroup ι₂ k)) :
    Set (GLCoord k ι₁ ⊗[k] GLCoord k ι₂ →ₐ[k] k) :=
  (fun p => tensorPointEquiv ((glPointEquiv p.1).ofConv, (glPointEquiv p.2).ofConv)) '' S

abbrev glPairPointSubgroup
    (H : Subgroup (Matrix.GeneralLinearGroup ι₁ k × Matrix.GeneralLinearGroup ι₂ k)) :
    Subgroup (WithConv (GLCoord k ι₁ ⊗[k] GLCoord k ι₂ →ₐ[k] k)) :=
  H.map glPairPointEquiv.toMonoidHom

theorem glPairPoints_eq
    (S : Set (Matrix.GeneralLinearGroup ι₁ k × Matrix.GeneralLinearGroup ι₂ k)) :
    glPairPoints S = transportPoints glPairPointEquiv S :=
  rfl

end Pair

section Product

structure FTHopfAlgebra (k : Type) [Field k] where
  carrier : Type
  [commRing : CommRing carrier]
  [hopfAlgebra : HopfAlgebra k carrier]
  [finiteType : Algebra.FiniteType k carrier]

attribute [instance] FTHopfAlgebra.commRing FTHopfAlgebra.hopfAlgebra FTHopfAlgebra.finiteType

variable (k) in
@[expose] def FTHopfAlgebra.unit : FTHopfAlgebra k :=
  ⟨k⟩

instance FTHopfAlgebra.subsingleton_unit_points :
    Subsingleton ((FTHopfAlgebra.unit k).carrier →ₐ[k] k) :=
  inferInstanceAs (Subsingleton (k →ₐ[k] k))

@[expose] def FTHopfAlgebra.tensor (A B : FTHopfAlgebra k) : FTHopfAlgebra k :=
  ⟨A.carrier ⊗[k] B.carrier⟩

variable (k) in
@[expose] def glProdCoord :
    (r : ℕ) → (ι : Fin r → Type) → [∀ i, Fintype (ι i)] → [∀ i, DecidableEq (ι i)] →
      FTHopfAlgebra k
  | 0, _, _, _ => FTHopfAlgebra.unit k
  | r + 1, ι, _, _ => FTHopfAlgebra.tensor ⟨GLCoord k (ι 0)⟩ (glProdCoord r fun i => ι i.succ)

@[expose] def piFinSuccMulEquiv {r : ℕ} (G : Fin (r + 1) → Type) [∀ i, Group (G i)] :
    (∀ i, G i) ≃* G 0 × ∀ i : Fin r, G i.succ where
  toFun f := (f 0, Fin.tail f)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by simp
  map_mul' _ _ := rfl

variable (k) in
@[expose] def glProdPointEquiv :
    (r : ℕ) → (ι : Fin r → Type) → [∀ i, Fintype (ι i)] → [∀ i, DecidableEq (ι i)] →
      (∀ i, Matrix.GeneralLinearGroup (ι i) k) ≃* WithConv ((glProdCoord k r ι).carrier →ₐ[k] k)
  | 0, _, _, _ =>
    { toFun _ := 1
      invFun _ := 1
      left_inv _ := Subsingleton.elim _ _
      right_inv _ := WithConv.ext
        (Subsingleton.elim (α := (FTHopfAlgebra.unit k).carrier →ₐ[k] k) _ _)
      map_mul' _ _ := (mul_one _).symm }
  | r + 1, ι, _, _ =>
    (piFinSuccMulEquiv fun i => Matrix.GeneralLinearGroup (ι i) k).trans
      ((glPointEquiv.prodCongr (glProdPointEquiv r fun i => ι i.succ)).trans
        tensorPointMulEquiv.symm)

theorem glProdPointEquiv_succ_apply (r : ℕ) (ι : Fin (r + 1) → Type) [∀ i, Fintype (ι i)]
    [∀ i, DecidableEq (ι i)] (g : ∀ i, Matrix.GeneralLinearGroup (ι i) k) :
    (glProdPointEquiv k (r + 1) ι g).ofConv =
      tensorPointEquiv ((glPointEquiv (g 0)).ofConv,
        (glProdPointEquiv k r (fun i => ι i.succ) (Fin.tail g)).ofConv) :=
  rfl

end Product

end CFSG.LieType.AlgebraicGroups
