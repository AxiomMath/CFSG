module

public import Mathlib
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.Open.Defs

public section

open CFSG.Open

namespace CFSG.ComponentClassification.PerfectAutomorphisms

theorem hom_eq_one_of_commutative {G H : Type*} [Group G] [Group H]
    [Group.IsPerfect G] [IsMulCommutative H] (homomorphism : G →* H) :
    homomorphism = 1 := by
  let : Group.IsPerfect homomorphism.range := Group.IsPerfect.range homomorphism
  have hsubsingleton : Subsingleton homomorphism.range := inferInstance
  ext element
  have hone : (⟨homomorphism element, ⟨element, rfl⟩⟩ : homomorphism.range) = 1 :=
    hsubsingleton.elim _ _
  exact congrArg Subtype.val hone

theorem hom_eq_id_of_central_displacement {G : Type*} [Group G] [Group.IsPerfect G]
    (homomorphism : G →* G)
    (hcentral : ∀ element : G, element⁻¹ * homomorphism element ∈ Subgroup.center G) :
    homomorphism = MonoidHom.id G := by
  let displacement : G →* Subgroup.center G :=
    { toFun := fun element => ⟨element⁻¹ * homomorphism element, hcentral element⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro left right
        apply Subtype.ext
        change (left * right)⁻¹ * homomorphism (left * right) =
          (left⁻¹ * homomorphism left) * (right⁻¹ * homomorphism right)
        have hcommutes := (Subgroup.mem_center_iff.mp (hcentral left)) right⁻¹
        calc
          (left * right)⁻¹ * homomorphism (left * right) =
              right⁻¹ * (left⁻¹ * homomorphism left) * homomorphism right := by
            rw [map_mul]
            group
          _ = (left⁻¹ * homomorphism left) * right⁻¹ * homomorphism right := by
            rw [hcommutes]
          _ = (left⁻¹ * homomorphism left) * (right⁻¹ * homomorphism right) := mul_assoc _ _ _ }
  have hdisplacement := hom_eq_one_of_commutative displacement
  ext element
  have hone : element⁻¹ * homomorphism element = 1 := by
    have hvalue := congrArg (fun homomorphism : G →* Subgroup.center G => homomorphism element)
      hdisplacement
    exact congrArg Subtype.val hvalue
  change homomorphism element = element
  exact (inv_mul_eq_one.mp hone).symm

@[expose] noncomputable def onCenterQuotient {G : Type*} [Group G] (automorphism : MulAut G) :
    MulAut (G ⧸ Subgroup.center G) :=
  QuotientGroup.congr (Subgroup.center G) (Subgroup.center G) automorphism
    ((Subgroup.characteristic_iff_map_eq.mp inferInstance) automorphism)

theorem onCenterQuotient_apply_mk {G : Type*} [Group G]
    (automorphism : MulAut G) (element : G) :
    (onCenterQuotient automorphism) ((QuotientGroup.mk' (Subgroup.center G)) element) =
      (QuotientGroup.mk' (Subgroup.center G)) (automorphism element) :=
  QuotientGroup.congr_mk (Subgroup.center G) (Subgroup.center G) automorphism _ element

@[expose] noncomputable def centerQuotientHom (G : Type*) [Group G] :
    MulAut G →* MulAut (G ⧸ Subgroup.center G) :=
  { toFun := onCenterQuotient
    map_one' := by
      ext element
      obtain ⟨lift, rfl⟩ := (QuotientGroup.mk'_surjective (Subgroup.center G)) element
      rw [onCenterQuotient_apply_mk]
      rfl
    map_mul' := by
      intro left right
      ext element
      obtain ⟨lift, rfl⟩ := (QuotientGroup.mk'_surjective (Subgroup.center G)) element
      rw [MulAut.mul_apply, onCenterQuotient_apply_mk, onCenterQuotient_apply_mk,
        onCenterQuotient_apply_mk]
      rfl }

theorem centerQuotientHom_conj {G : Type*} [Group G] (g : G) :
    centerQuotientHom G (MulAut.conj g) =
      MulAut.conj (QuotientGroup.mk' (Subgroup.center G) g) := by
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) x
  change onCenterQuotient (MulAut.conj g) (QuotientGroup.mk' (Subgroup.center G) y) =
    MulAut.conj (QuotientGroup.mk' (Subgroup.center G) g)
      (QuotientGroup.mk' (Subgroup.center G) y)
  rw [onCenterQuotient_apply_mk, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_inv,
    ← map_mul]

theorem onCenterQuotient_eq_one_imp {G : Type*} [Group G] [Group.IsPerfect G]
    (automorphism : MulAut G) (hquotient : onCenterQuotient automorphism = 1) :
    automorphism = 1 := by
  have hcentral : ∀ element : G, element⁻¹ * automorphism element ∈ Subgroup.center G := by
    intro element
    have hfixed : (QuotientGroup.mk' (Subgroup.center G)) (automorphism element) =
        (QuotientGroup.mk' (Subgroup.center G)) element := by
      have hdescend : (onCenterQuotient automorphism)
          ((QuotientGroup.mk' (Subgroup.center G)) element) =
          (QuotientGroup.mk' (Subgroup.center G)) (automorphism element) :=
        QuotientGroup.congr_mk (Subgroup.center G) (Subgroup.center G) automorphism _ element
      rw [← hdescend, hquotient]
      rfl
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (Subgroup.center G)) (element⁻¹ * automorphism element) = 1
    rw [map_mul, map_inv, hfixed, inv_mul_cancel]
  have hidentity := hom_eq_id_of_central_displacement automorphism.toMonoidHom hcentral
  ext element
  exact congrArg (fun homomorphism : G →* G => homomorphism element) hidentity

theorem centerQuotientHom_injective (G : Type*) [Group G] [Group.IsPerfect G] :
    Function.Injective (centerQuotientHom G) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro automorphism hmem
  exact Subgroup.mem_bot.mpr (onCenterQuotient_eq_one_imp automorphism hmem)

end CFSG.ComponentClassification.PerfectAutomorphisms
