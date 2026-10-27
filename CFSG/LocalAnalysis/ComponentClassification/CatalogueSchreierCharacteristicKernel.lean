module

public import CFSG.Permutation.FiveTransitive.CharacteristicAutomorphism
public import Mathlib.GroupTheory.Solvable
public import Mathlib.Tactic.Group

public section

namespace CFSG.ComponentClassification.CatalogueSchreierCharacteristic

open CFSG.FiveTransitive.CharacteristicAutomorphism

variable {H : Type*} [Group H]

@[expose] def pointwiseKernel (D : Subgroup H) [D.Characteristic] :
    Subgroup (MulAut H) := (restrict D).ker

theorem mem_pointwiseKernel_iff (D : Subgroup H) [D.Characteristic]
    (automorphism : MulAut H) :
    automorphism ∈ pointwiseKernel D ↔
      ∀ element ∈ D, automorphism element = element := by
  constructor
  · intro hautomorphism element helement
    have hrestriction : restrict D automorphism = 1 := hautomorphism
    exact congrArg (fun restriction : MulAut D =>
      ((restriction ⟨element, helement⟩ : D) : H)) hrestriction
  · intro hfix
    change restrict D automorphism = 1
    apply MulEquiv.ext
    intro element
    exact Subtype.ext (hfix element element.property)

theorem pointwiseKernel_fixes (D : Subgroup H) [D.Characteristic]
    (automorphism : pointwiseKernel D) (element : H) (helement : element ∈ D) :
    (automorphism : MulAut H) element = element :=
  (mem_pointwiseKernel_iff D automorphism).mp automorphism.property element helement

theorem displacement_mem_centralizer (D : Subgroup H) [D.Characteristic]
    (automorphism : pointwiseKernel D) (element : H) :
    element⁻¹ * (automorphism : MulAut H) element ∈ Subgroup.centralizer (D : Set H) := by
  apply Subgroup.mem_centralizer_iff.mpr
  intro member hmember
  have hconjugate : element * member * element⁻¹ ∈ D :=
    (inferInstance : D.Normal).conj_mem member hmember element
  have hfixed := pointwiseKernel_fixes D automorphism
    (element * member * element⁻¹) hconjugate
  have hconjugation : element * member * element⁻¹ =
      (automorphism : MulAut H) element * member *
        ((automorphism : MulAut H) element)⁻¹ := by
    simpa only [map_mul, map_inv, pointwiseKernel_fixes D automorphism member hmember]
      using hfixed.symm
  calc
    member * (element⁻¹ * (automorphism : MulAut H) element) =
        element⁻¹ * (element * member * element⁻¹) *
          (automorphism : MulAut H) element := by group
    _ = element⁻¹ * ((automorphism : MulAut H) element * member *
          ((automorphism : MulAut H) element)⁻¹) *
          (automorphism : MulAut H) element := by rw [hconjugation]
    _ = (element⁻¹ * (automorphism : MulAut H) element) * member := by group

@[expose] def displacement (D : Subgroup H) [D.Characteristic]
    (hcentralizer : Subgroup.centralizer (D : Set H) ≤ D)
    (automorphism : pointwiseKernel D) (element : H) : Subgroup.center D :=
  ⟨⟨element⁻¹ * (automorphism : MulAut H) element,
      hcentralizer (displacement_mem_centralizer D automorphism element)⟩,
    Subgroup.mem_center_iff.mpr fun member => Subtype.ext
      (Subgroup.mem_centralizer_iff.mp
        (displacement_mem_centralizer D automorphism element) member member.property)⟩

@[simp] theorem displacement_coe (D : Subgroup H) [D.Characteristic]
    (hcentralizer : Subgroup.centralizer (D : Set H) ≤ D)
    (automorphism : pointwiseKernel D) (element : H) :
    ((displacement D hcentralizer automorphism element : D) : H) =
      element⁻¹ * (automorphism : MulAut H) element := rfl

@[expose] def displacementHom (D : Subgroup H) [D.Characteristic]
    (hcentralizer : Subgroup.centralizer (D : Set H) ≤ D) :
    pointwiseKernel D →* (H → Subgroup.center D) where
  toFun automorphism := displacement D hcentralizer automorphism
  map_one' := by
    funext element
    apply Subtype.ext
    apply Subtype.ext
    change element⁻¹ * (1 : MulAut H) element = 1
    simp
  map_mul' := by
    intro left right
    funext element
    apply Subtype.ext
    apply Subtype.ext
    change element⁻¹ * ((left : MulAut H) * (right : MulAut H)) element =
      (element⁻¹ * (left : MulAut H) element) *
        (element⁻¹ * (right : MulAut H) element)
    rw [MulAut.mul_apply]
    have hdisplacement : element⁻¹ * (right : MulAut H) element ∈ D :=
      hcentralizer (displacement_mem_centralizer D right element)
    have hfixed := pointwiseKernel_fixes D left _ hdisplacement
    have helement : (right : MulAut H) element =
        element * (element⁻¹ * (right : MulAut H) element) := by group
    calc
      element⁻¹ * (left : MulAut H) ((right : MulAut H) element) =
          element⁻¹ * (left : MulAut H)
            (element * (element⁻¹ * (right : MulAut H) element)) :=
        congrArg (fun member => element⁻¹ * (left : MulAut H) member) helement
      _ = (element⁻¹ * (left : MulAut H) element) *
          (element⁻¹ * (right : MulAut H) element) := by
        rw [map_mul, hfixed, mul_assoc]

theorem displacementHom_injective (D : Subgroup H) [D.Characteristic]
    (hcentralizer : Subgroup.centralizer (D : Set H) ≤ D) :
    Function.Injective (displacementHom D hcentralizer) := by
  intro left right hequal
  apply Subtype.ext
  apply MulEquiv.ext
  intro element
  have hvalue := congrArg
    (fun function : H → Subgroup.center D => ((function element : D) : H)) hequal
  change element⁻¹ * (left : MulAut H) element =
    element⁻¹ * (right : MulAut H) element at hvalue
  exact mul_left_cancel hvalue

theorem pointwiseKernel_mul_comm (D : Subgroup H) [D.Characteristic]
    (hcentralizer : Subgroup.centralizer (D : Set H) ≤ D)
    (left right : pointwiseKernel D) : left * right = right * left := by
  apply displacementHom_injective D hcentralizer
  rw [map_mul, map_mul]
  exact mul_comm' _ _

theorem pointwiseKernel_isMulCommutative (D : Subgroup H) [D.Characteristic]
    (hcentralizer : Subgroup.centralizer (D : Set H) ≤ D) :
    IsMulCommutative (pointwiseKernel D) :=
  isMulCommutative_iff.mpr (pointwiseKernel_mul_comm D hcentralizer)

theorem pointwiseKernel_solvable (D : Subgroup H) [D.Characteristic]
    (hcentralizer : Subgroup.centralizer (D : Set H) ≤ D) :
    Group.IsSolvable (pointwiseKernel D) :=
  Group.isSolvable_of_isSolvable_injective (displacementHom_injective D hcentralizer)

end CFSG.ComponentClassification.CatalogueSchreierCharacteristic
