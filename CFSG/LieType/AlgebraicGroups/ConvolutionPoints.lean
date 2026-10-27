module

public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
public import Mathlib.Algebra.Group.Ext

public noncomputable section

open WithConv Coalgebra

namespace CFSG.ConvolutionPoints

attribute [scoped instance high] AlgHom.convInv AlgHom.convGroup
  AlgHom.instCommGroupWithConvOfIsCocomm

end CFSG.ConvolutionPoints

namespace CFSG.LieType.AlgebraicGroups

variable {R A C : Type*} [CommSemiring R] [CommSemiring A] [HopfAlgebra R A] [CommSemiring C]
  [Bialgebra R C]

theorem tauCetiGroup_eq :
    (TauCeti.AlgHom.instGroup : Group (WithConv (A →ₐ[R] C))) = AlgHom.convGroup :=
  Group.ext rfl

theorem tauCetiCommGroup_eq [IsCocomm R A] :
    (TauCeti.AlgHom.instCommGroup : CommGroup (WithConv (A →ₐ[R] C))) =
      AlgHom.instCommGroupWithConvOfIsCocomm :=
  CommGroup.ext rfl

open scoped CFSG.ConvolutionPoints in
theorem tauCeti_inv_eq (f : WithConv (A →ₐ[R] C)) :
    (letI := (TauCeti.AlgHom.instInv : Inv (WithConv (A →ₐ[R] C))); f⁻¹) = f⁻¹ :=
  congrArg (fun G : Group (WithConv (A →ₐ[R] C)) => G.inv f) tauCetiGroup_eq

open scoped CFSG.ConvolutionPoints in
theorem tauCeti_div_eq (f g : WithConv (A →ₐ[R] C)) :
    (letI := (TauCeti.AlgHom.instGroup : Group (WithConv (A →ₐ[R] C))); f / g) = f / g :=
  congrArg (fun G : Group (WithConv (A →ₐ[R] C)) => G.div f g) tauCetiGroup_eq

open scoped CFSG.ConvolutionPoints in
theorem tauCeti_zpow_eq (f : WithConv (A →ₐ[R] C)) (n : ℤ) :
    (letI := (TauCeti.AlgHom.instGroup : Group (WithConv (A →ₐ[R] C))); f ^ n) = f ^ n :=
  congrArg (fun G : Group (WithConv (A →ₐ[R] C)) => G.zpow n f) tauCetiGroup_eq

theorem toConv_comp_antipodeAlgHom {F : Type*} [CommSemiring F] [Algebra R F] (φ : A →ₐ[R] F) :
    toConv (φ.comp (HopfAlgebra.antipodeAlgHom R A)) = (toConv φ)⁻¹ :=
  ofConv_injective <| AlgHom.ext fun x => (TauCeti.AlgHom.convInv_apply (toConv φ) x).symm

def toTauCetiSubgroup (S : @Subgroup (WithConv (A →ₐ[R] C)) AlgHom.convGroup) :
    Subgroup (WithConv (A →ₐ[R] C)) where
  carrier := S
  mul_mem' := @Subgroup.mul_mem _ AlgHom.convGroup S
  one_mem' := @Subgroup.one_mem _ AlgHom.convGroup S
  inv_mem' := fun {f} hf => by
    rw [tauCeti_inv_eq]
    exact @Subgroup.inv_mem _ AlgHom.convGroup S f hf

open scoped CFSG.ConvolutionPoints in
def ofTauCeti :
    @Subgroup (WithConv (A →ₐ[R] C)) TauCeti.AlgHom.instGroup ≃o
      Subgroup (WithConv (A →ₐ[R] C)) where
  toFun S :=
    { carrier := S
      mul_mem' := @Subgroup.mul_mem _ TauCeti.AlgHom.instGroup S
      one_mem' := @Subgroup.one_mem _ TauCeti.AlgHom.instGroup S
      inv_mem' := fun {f} hf => by
        rw [← tauCeti_inv_eq]
        exact @Subgroup.inv_mem _ TauCeti.AlgHom.instGroup S f hf }
  invFun := toTauCetiSubgroup
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

open scoped CFSG.ConvolutionPoints in
@[simp]
theorem mem_ofTauCeti {S : @Subgroup (WithConv (A →ₐ[R] C)) TauCeti.AlgHom.instGroup}
    {f : WithConv (A →ₐ[R] C)} : f ∈ ofTauCeti S ↔ f ∈ S :=
  Iff.rfl

open scoped CFSG.ConvolutionPoints in
@[simp]
theorem mem_ofTauCeti_symm {S : Subgroup (WithConv (A →ₐ[R] C))} {f : WithConv (A →ₐ[R] C)} :
    f ∈ ofTauCeti.symm S ↔ f ∈ S :=
  Iff.rfl

open scoped CFSG.ConvolutionPoints in
def subgroupMulEquiv (S : @Subgroup (WithConv (A →ₐ[R] C)) TauCeti.AlgHom.instGroup) :
    S ≃* ofTauCeti S where
  toFun x := ⟨x, x.2⟩
  invFun x := ⟨x, x.2⟩
  map_mul' _ _ := rfl

