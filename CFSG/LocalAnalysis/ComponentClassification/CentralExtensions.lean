module

public import Mathlib
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.Open.Defs
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.LocalAnalysis.ComponentClassification.Layer
public import CFSG.LocalAnalysis.ComponentClassification.TwoResidual

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.ComponentClassification.CentralExtensions

theorem commutator_mul_center_left {G : Type*} [Group G] (left central right : G)
    (hcentral : central ∈ Subgroup.center G) : ⁅left * central, right⁆ = ⁅left, right⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul,
    (show Commute central right from ((Subgroup.mem_center_iff.mp hcentral) right).symm).commutator_eq]
  simp

theorem commutator_mul_center_right {G : Type*} [Group G] (left right central : G)
    (hcentral : central ∈ Subgroup.center G) : ⁅left, right * central⁆ = ⁅left, right⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj,
    (show Commute left central from (Subgroup.mem_center_iff.mp hcentral) left).commutator_eq]
  simp

theorem commutator_sup_central {G : Type*} [Group G] (subgroup centralSubgroup : Subgroup G)
    [centralSubgroup.Normal] (hcentral : centralSubgroup ≤ Subgroup.center G) :
    ⁅subgroup ⊔ centralSubgroup, subgroup ⊔ centralSubgroup⁆ = ⁅subgroup, subgroup⁆ := by
  apply le_antisymm
  · apply Subgroup.commutator_le.mpr
    intro left hleft right hright
    obtain ⟨leftMember, hleftMember, leftCentral, hleftCentral, rfl⟩ :=
      Subgroup.mem_sup_of_normal_right.mp hleft
    obtain ⟨rightMember, hrightMember, rightCentral, hrightCentral, rfl⟩ :=
      Subgroup.mem_sup_of_normal_right.mp hright
    rw [commutator_mul_center_left _ _ _ (hcentral hleftCentral),
      commutator_mul_center_right _ _ _ (hcentral hrightCentral)]
    exact Subgroup.commutator_mem_commutator hleftMember hrightMember
  · exact Subgroup.commutator_mono le_sup_left le_sup_left

theorem derived_map_eq_top {G H : Type*} [Group G] [Group H] [Group.IsPerfect H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient) :
    (commutator G).map quotient = ⊤ := by
  rw [commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective quotient hsurjective]
  exact Group.IsPerfect.commutator_eq_top

theorem derived_sup_center_eq_top {G H : Type*} [Group G] [Group H]
    [Group.IsPerfect H] (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hcentralKernel : quotient.ker ≤ Subgroup.center G) :
    commutator G ⊔ Subgroup.center G = ⊤ := by
  have hcomap := Subgroup.comap_map_eq quotient (commutator G)
  rw [derived_map_eq_top quotient hsurjective, Subgroup.comap_top] at hcomap
  exact top_unique (hcomap.trans_le (sup_le_sup_left hcentralKernel _))

theorem derived_perfect {G H : Type*} [Group G] [Group H] [Group.IsPerfect H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hcentralKernel : quotient.ker ≤ Subgroup.center G) :
    Group.IsPerfect (commutator G) := by
  have hsup := derived_sup_center_eq_top quotient hsurjective hcentralKernel
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm (Subgroup.commutator_le_self _) _
  rw [commutator_def]
  apply Subgroup.commutator_le.mpr
  intro left _ right _
  have hleft : left ∈ commutator G ⊔ Subgroup.center G := by
    rw [hsup]
    exact Subgroup.mem_top _
  have hright : right ∈ commutator G ⊔ Subgroup.center G := by
    rw [hsup]
    exact Subgroup.mem_top _
  obtain ⟨leftDerived, hleftDerived, leftCentral, hleftCentral, rfl⟩ :=
    Subgroup.mem_sup_of_normal_left.mp hleft
  obtain ⟨rightDerived, hrightDerived, rightCentral, hrightCentral, rfl⟩ :=
    Subgroup.mem_sup_of_normal_left.mp hright
  rw [commutator_mul_center_left _ _ _ hleftCentral,
    commutator_mul_center_right _ _ _ hrightCentral]
  exact Subgroup.commutator_mem_commutator hleftDerived hrightDerived

theorem quasisimple_of_surjective {G H : Type*} [Group G] [Group H] [Group.IsPerfect G]
    (hquasisimple : IsQuasisimple H) (quotient : G →* H)
    (hsurjective : Function.Surjective quotient)
    (hcentralKernel : quotient.ker ≤ Subgroup.center G) : IsQuasisimple G := by
  let : IsSimpleGroup (H ⧸ Subgroup.center H) := hquasisimple.2
  let centralQuotient := (QuotientGroup.mk' (Subgroup.center H)).comp quotient
  have hkernel : centralQuotient.ker = Subgroup.center G := by
    have hcomap : centralQuotient.ker = (Subgroup.center H).comap quotient := by
      ext element
      change (QuotientGroup.mk' (Subgroup.center H)) (quotient element) = 1 ↔
        quotient element ∈ Subgroup.center H
      exact QuotientGroup.eq_one_iff _
    rw [hcomap]
    exact Quasisimple.center_comap_of_central_kernel quotient hsurjective hcentralKernel
  have hcentralSurjective : Function.Surjective centralQuotient :=
    (QuotientGroup.mk'_surjective _).comp hsurjective
  exact ⟨Group.IsPerfect.commutator_eq_top,
    (QuotientGroup.liftEquiv (Subgroup.center G) hcentralSurjective hkernel.symm).isSimpleGroup⟩

theorem derived_quasisimple {G H : Type*} [Group G] [Group H]
    (hquasisimple : IsQuasisimple H) (quotient : G →* H)
    (hsurjective : Function.Surjective quotient)
    (hcentralKernel : quotient.ker ≤ Subgroup.center G) :
    IsQuasisimple (commutator G) := by
  let : Group.IsPerfect H := ⟨hquasisimple.1⟩
  let : Group.IsPerfect (commutator G) := derived_perfect quotient hsurjective hcentralKernel
  have hrestriction : Function.Surjective (quotient.domRestrict (commutator G)) := by
    intro element
    have hmem : element ∈ (commutator G).map quotient := by
      rw [derived_map_eq_top quotient hsurjective]
      exact Subgroup.mem_top _
    obtain ⟨lift, hmem, hlift⟩ := Subgroup.mem_map.mp hmem
    exact ⟨⟨lift, hmem⟩, hlift⟩
  have hkernel : (quotient.domRestrict (commutator G)).ker ≤
      Subgroup.center (commutator G) := by
    intro element hmem
    have hcentral : element.val ∈ Subgroup.center G := hcentralKernel hmem
    apply Subgroup.mem_center_iff.mpr
    intro other
    exact Subtype.ext ((Subgroup.mem_center_iff.mp hcentral) other.val)
  exact quasisimple_of_surjective hquasisimple (quotient.domRestrict (commutator G))
    hrestriction hkernel

end CFSG.ComponentClassification.CentralExtensions
