module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexUnitCoordinates
public import Mathlib.GroupTheory.SemidirectProduct

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

universe v

variable {G : Type v} [Group G]

@[expose] def unitAffineGroup (U : Subgroup G) :=
  SemidirectProduct U (MulAut U) (MonoidHom.id (MulAut U))

instance unitAffineGroupGroup (U : Subgroup G) : Group (unitAffineGroup U) :=
  inferInstanceAs (Group (SemidirectProduct U (MulAut U) (MonoidHom.id (MulAut U))))

@[expose] def unitAffinePerm (U : Subgroup G) : unitAffineGroup U →* Equiv.Perm U where
  toFun a := a.right.toEquiv.trans (Equiv.mulLeft a.left)
  map_one' := by
    apply Equiv.ext
    intro x
    exact one_mul x
  map_mul' a b := by
    apply Equiv.ext
    intro x
    change (a.left * a.right b.left) * (a.right (b.right x)) =
      a.left * a.right (b.left * b.right x)
    rw [map_mul, mul_assoc]

theorem unitAffinePerm_apply (U : Subgroup G) (a : unitAffineGroup U) (x : U) :
    unitAffinePerm U a x = a.left * a.right x := rfl

theorem unitAffinePerm_injective (U : Subgroup G) :
    Function.Injective (unitAffinePerm U) := by
  intro a b hab
  have hleft : a.left = b.left := by
    have heq := congrArg (fun e : Equiv.Perm U => e 1) hab
    simpa only [unitAffinePerm_apply, map_one, mul_one] using heq
  have hright : a.right = b.right := by
    apply MulEquiv.ext
    intro x
    have heq := congrArg (fun e : Equiv.Perm U => e x) hab
    rw [unitAffinePerm_apply, unitAffinePerm_apply, hleft] at heq
    exact mul_left_cancel heq
  exact SemidirectProduct.ext hleft hright

@[expose] def unitAffineHom (U : Subgroup G) (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x) :
    Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G)) →* unitAffineGroup U where
  toFun n := ⟨unitCoordinatePerm U u n 1, unitLinearConjugation U u hu hcentral n⟩
  map_one' := by
    apply SemidirectProduct.ext
    · exact congrArg (fun e : Equiv.Perm U => e 1) ((unitCoordinatePerm U u).map_one)
    · exact (unitLinearConjugation U u hu hcentral).map_one
  map_mul' n m := by
    apply SemidirectProduct.ext
    · exact unitCoordinatePerm_displacement_mul U u hu hcentral n m
    · exact (unitLinearConjugation U u hu hcentral).map_mul n m

theorem unitAffineHom_left (U : Subgroup G) (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x)
    (n : Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G))) :
    (unitAffineHom U u hu hcentral n).left = unitCoordinatePerm U u n 1 := rfl

theorem unitAffineHom_right (U : Subgroup G) (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x)
    (n : Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G))) :
    (unitAffineHom U u hu hcentral n).right = unitLinearConjugation U u hu hcentral n := rfl

theorem unitAffinePerm_comp_unitAffineHom (U : Subgroup G) (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x) :
    (unitAffinePerm U).comp (unitAffineHom U u hu hcentral) = unitCoordinatePerm U u := by
  apply DFunLike.ext
  intro n
  apply Equiv.ext
  intro x
  exact (unitCoordinatePerm_displacement_mul_conjugation U u hu hcentral n x).symm

theorem unitAffineHom_ker_eq_coordinate_ker (U : Subgroup G) (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x) :
    (unitAffineHom U u hu hcentral).ker = (unitCoordinatePerm U u).ker := by
  rw [← unitAffinePerm_comp_unitAffineHom U u hu hcentral]
  exact (MonoidHom.ker_comp_of_injective _ _ (unitAffinePerm_injective U)).symm

theorem unitAffineHom_ker (U : Subgroup G) (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x) :
    (unitAffineHom U u hu hcentral).ker =
      (Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer (U : Set G)).subgroupOf
        (Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G))) := by
  rw [unitAffineHom_ker_eq_coordinate_ker, unitCoordinatePerm_ker]

theorem unitAffineHom_ker_map (U : Subgroup G) (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x) :
    (unitAffineHom U u hu hcentral).ker.map
        (Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G))).subtype =
      Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer (U : Set G) := by
  rw [unitAffineHom_ker_eq_coordinate_ker, unitCoordinatePerm_ker_map]

@[expose] def unitAffineQuotientEquivRange (U : Subgroup G) (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x) :
    Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G)) ⧸
        (unitAffineHom U u hu hcentral).ker ≃*
      (unitAffineHom U u hu hcentral).range :=
  QuotientGroup.quotientKerEquivRange (unitAffineHom U u hu hcentral)

theorem entire_coset_centralizer_index_eq_affine_image_card (U : Subgroup G) (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x) :
    (Subgroup.centralizer ((fun x : G => u * x) '' (U : Set G))).relIndex
        (Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G))) =
      Nat.card (unitAffineHom U u hu hcentral).range := by
  change ((Subgroup.centralizer ((fun x : G => u * x) '' (U : Set G))).subgroupOf
    (Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G)))).index = _
  rw [unit_translate_entire_centralizer, ← unitAffineHom_ker U u hu hcentral,
    Subgroup.index_ker]

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
