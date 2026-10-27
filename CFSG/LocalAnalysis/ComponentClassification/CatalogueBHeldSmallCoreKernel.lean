module

public import CFSG.GroupTheory.AutomorphismRestrictionKernel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierCharacteristicKernel

public section

namespace CFSG.ComponentClassification.CatalogueBHeldSmallCore

open CFSG.FiveTransitive.CharacteristicAutomorphism

variable {G : Type*} [Group G]

@[expose] def jointKernel (A : Subgroup G) [A.Characteristic] :
    Subgroup (MulAut G) := (CFSG.characteristicRestrictionQuotient A).ker

theorem jointKernel_eq (A : Subgroup G) [A.Characteristic] :
    jointKernel A = (restrict A).ker ⊓ (quotient A).ker :=
  CFSG.characteristicRestrictionQuotient_ker A

@[expose] def jointKernelToPointwise (A : Subgroup G) [A.Characteristic] :
    jointKernel A →* CatalogueSchreierCharacteristic.pointwiseKernel A :=
  Subgroup.inclusion (by rw [jointKernel_eq]; exact inf_le_left)

theorem jointKernel_fixes (A : Subgroup G) [A.Characteristic]
    (automorphism : jointKernel A) (element : G) (helement : element ∈ A) :
    (automorphism : MulAut G) element = element :=
  CatalogueSchreierCharacteristic.pointwiseKernel_fixes A
    (jointKernelToPointwise A automorphism) element helement

theorem jointKernel_quotient_fixed (A : Subgroup G) [A.Characteristic]
    (automorphism : jointKernel A) (element : G) :
    (QuotientGroup.mk' A) ((automorphism : MulAut G) element) =
      (QuotientGroup.mk' A) element := by
  have hquotient : quotient A (automorphism : MulAut G) = 1 :=
    (show (automorphism : MulAut G) ∈
      (restrict A).ker ⊓ (quotient A).ker from by
        rw [← jointKernel_eq]; exact automorphism.property).2
  have hvalue := congrArg
    (fun action : MulAut (G ⧸ A) => action ((QuotientGroup.mk' A) element)) hquotient
  simpa only [quotient_apply_mk, MulAut.one_apply] using hvalue

theorem jointKernel_displacement_mem (A : Subgroup G) [A.Characteristic]
    (automorphism : jointKernel A) (element : G) :
    element⁻¹ * (automorphism : MulAut G) element ∈ A := by
  have hvalue : (QuotientGroup.mk' A)
      (element⁻¹ * (automorphism : MulAut G) element) = 1 := by
    rw [map_mul, map_inv, jointKernel_quotient_fixed]
    exact inv_mul_cancel _
  simpa only [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] using hvalue

@[expose] def jointDisplacement (A : Subgroup G) [A.Characteristic]
    (automorphism : jointKernel A) (element : G) : Subgroup.center A :=
  ⟨⟨element⁻¹ * (automorphism : MulAut G) element,
      jointKernel_displacement_mem A automorphism element⟩,
    Subgroup.mem_center_iff.mpr fun member => Subtype.ext
      (Subgroup.mem_centralizer_iff.mp
        (CatalogueSchreierCharacteristic.displacement_mem_centralizer A
          (jointKernelToPointwise A automorphism) element) member member.property)⟩

@[simp] theorem jointDisplacement_coe (A : Subgroup G) [A.Characteristic]
    (automorphism : jointKernel A) (element : G) :
    ((jointDisplacement A automorphism element : A) : G) =
      element⁻¹ * (automorphism : MulAut G) element := rfl

@[expose] def jointDisplacementHom (A : Subgroup G) [A.Characteristic] :
    jointKernel A →* (G → Subgroup.center A) where
  toFun automorphism := jointDisplacement A automorphism
  map_one' := by
    funext element
    apply Subtype.ext
    apply Subtype.ext
    change element⁻¹ * (1 : MulAut G) element = 1
    simp
  map_mul' := by
    intro left right
    funext element
    apply Subtype.ext
    apply Subtype.ext
    change element⁻¹ * ((left : MulAut G) * (right : MulAut G)) element =
      (element⁻¹ * (left : MulAut G) element) *
        (element⁻¹ * (right : MulAut G) element)
    rw [MulAut.mul_apply]
    have hfixed := jointKernel_fixes A left _
      (jointKernel_displacement_mem A right element)
    have helement : (right : MulAut G) element =
        element * (element⁻¹ * (right : MulAut G) element) := by group
    calc
      element⁻¹ * (left : MulAut G) ((right : MulAut G) element) =
          element⁻¹ * (left : MulAut G)
            (element * (element⁻¹ * (right : MulAut G) element)) :=
        congrArg (fun member => element⁻¹ * (left : MulAut G) member) helement
      _ = (element⁻¹ * (left : MulAut G) element) *
          (element⁻¹ * (right : MulAut G) element) := by
        rw [map_mul, hfixed, mul_assoc]

theorem jointDisplacementHom_injective (A : Subgroup G) [A.Characteristic] :
    Function.Injective (jointDisplacementHom A) := by
  intro left right hequal
  apply Subtype.ext
  apply MulEquiv.ext
  intro element
  have hvalue := congrArg
    (fun function : G → Subgroup.center A => ((function element : A) : G)) hequal
  change element⁻¹ * (left : MulAut G) element =
    element⁻¹ * (right : MulAut G) element at hvalue
  exact mul_left_cancel hvalue

theorem jointKernel_isMulCommutative (A : Subgroup G) [A.Characteristic] :
    IsMulCommutative (jointKernel A) := by
  apply IsMulCommutative.of_comm
  intro left right
  apply jointDisplacementHom_injective A
  rw [map_mul, map_mul]
  exact mul_comm' _ _

theorem jointKernel_solvable (A : Subgroup G) [A.Characteristic] :
    Group.IsSolvable (jointKernel A) :=
  Group.isSolvable_of_isSolvable_injective (jointDisplacementHom_injective A)

theorem automorphism_solvable_of_sections (A : Subgroup G) [A.Characteristic]
    [Group.IsSolvable (MulAut A)] [Group.IsSolvable (MulAut (G ⧸ A))] :
    Group.IsSolvable (MulAut G) := by
  let : Group.IsSolvable (jointKernel A) := jointKernel_solvable A
  exact Group.isSolvable_of_ker_le_range (jointKernel A).subtype
    (CFSG.characteristicRestrictionQuotient A) (by rw [Subgroup.range_subtype]; rfl)

end CFSG.ComponentClassification.CatalogueBHeldSmallCore
