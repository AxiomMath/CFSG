module

public import Mathlib
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.ComponentClassification.SolvableKernelContainment

theorem perfect_solvable_subsingleton {G : Type*} [Group G]
    [Group.IsPerfect G] [Group.IsSolvable G] : Subsingleton G := by
  rcases subsingleton_or_nontrivial G with hsubsingleton | hnontrivial
  · exact hsubsingleton
  · let : Nontrivial G := hnontrivial
    exact (Group.IsPerfect.not_isSolvable G inferInstance).elim

theorem perfect_containment {G H : Type*} [Group G] [Group H]
    (quotient : G →* H) [Group.IsSolvable quotient.ker]
    (perfectSubgroup containingSubgroup : Subgroup G)
    [Group.IsPerfect perfectSubgroup] [containingSubgroup.Normal]
    (himages : perfectSubgroup.map quotient ≤ containingSubgroup.map quotient) :
    perfectSubgroup ≤ containingSubgroup := by
  let projection := QuotientGroup.mk' containingSubgroup
  have hpreimage := Subgroup.map_le_iff_le_comap.mp himages
  rw [Subgroup.comap_map_eq] at hpreimage
  have hprojection : perfectSubgroup.map projection ≤ quotient.ker.map projection := by
    have hmap := Subgroup.map_mono (f := projection) hpreimage
    rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff containingSubgroup).mpr
      (show containingSubgroup ≤ projection.ker by rw [QuotientGroup.ker_mk']), bot_sup_eq] at hmap
    exact hmap
  let kernelImage := quotient.ker.map projection
  let kernelRestriction : quotient.ker →* kernelImage :=
    (projection.domRestrict quotient.ker).codRestrict kernelImage
      fun element => Subgroup.mem_map_of_mem projection element.property
  have hsurjective : Function.Surjective kernelRestriction := by
    intro element
    obtain ⟨lift, hmem, hvalue⟩ := Subgroup.mem_map.mp element.property
    exact ⟨⟨lift, hmem⟩, Subtype.ext hvalue⟩
  let : Group.IsSolvable kernelImage := Group.isSolvable_of_surjective hsurjective
  let : Group.IsSolvable (perfectSubgroup.map projection) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hprojection)
  let : Group.IsPerfect (perfectSubgroup.map projection) := Group.IsPerfect.map projection
  have hsubsingleton : Subsingleton (perfectSubgroup.map projection) := perfect_solvable_subsingleton
  have hbot : perfectSubgroup.map projection = ⊥ := by
    apply le_antisymm _ bot_le
    intro element hmem
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val
      (hsubsingleton.elim (⟨element, hmem⟩ : perfectSubgroup.map projection) 1))
  have hkernel := (Subgroup.map_eq_bot_iff _).mp hbot
  rwa [QuotientGroup.ker_mk'] at hkernel

theorem hom_eq_one {G H : Type*} [Group G] [Group H]
    [Group.IsPerfect G] [Group.IsSolvable H] (homomorphism : G →* H) : homomorphism = 1 := by
  let : Group.IsPerfect homomorphism.range := Group.IsPerfect.range homomorphism
  have hsubsingleton : Subsingleton homomorphism.range := perfect_solvable_subsingleton
  apply MonoidHom.ext
  intro element
  exact congrArg Subtype.val
    (hsubsingleton.elim (⟨homomorphism element, ⟨element, rfl⟩⟩ : homomorphism.range) 1)

end CFSG.ComponentClassification.SolvableKernelContainment
