module

public import Mathlib
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.Open.Defs
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.LocalAnalysis.ComponentClassification.Components

public section

open CFSG.Open

namespace CFSG.ComponentClassification.Quasisimple

theorem simple_of_perfect (G : Type*) [Group G] [IsSimpleGroup G] [Group.IsPerfect G] :
    IsQuasisimple G := by
  have hnonab : ∃ left right : G, left * right ≠ right * left := by
    by_contra hcommutes
    let : IsMulCommutative G := isMulCommutative_iff.mpr (by
      intro left right
      exact not_ne_iff.mp (fun hne => hcommutes ⟨left, right, hne⟩))
    have hsubsingleton : Subsingleton G := inferInstance
    exact not_subsingleton G hsubsingleton
  have hcenter := Helpers.center_eq_bot G hnonab
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  exact ((QuotientGroup.congr (Subgroup.center G) ⊥ (MulEquiv.refl G)
    (by
      change (Subgroup.center G).map (MonoidHom.id G) = ⊥
      rwa [Subgroup.map_id])).trans
      (QuotientGroup.quotientBot (G := G))).isSimpleGroup

theorem normal_le_center_or_eq_top {G : Type*} [Group G]
    (hquasisimple : IsQuasisimple G) (subgroup : Subgroup G) [subgroup.Normal] :
    subgroup ≤ Subgroup.center G ∨ subgroup = ⊤ := by
  let quotient := QuotientGroup.mk' (Subgroup.center G)
  let : IsSimpleGroup (G ⧸ Subgroup.center G) := hquasisimple.2
  have hnormal : (subgroup.map quotient).Normal :=
    Subgroup.Normal.map inferInstance quotient (QuotientGroup.mk'_surjective _)
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  · left
    have hkernel : subgroup ≤ quotient.ker := subgroup.map_eq_bot_iff.mp hbot
    change subgroup ≤ (QuotientGroup.mk' (Subgroup.center G)).ker at hkernel
    simpa only [QuotientGroup.ker_mk'] using hkernel
  · right
    have hsup : subgroup ⊔ Subgroup.center G = ⊤ := by
      have hcomap := Subgroup.comap_map_eq quotient subgroup
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
      exact hcomap.symm
    have hderived : commutator G ≤ subgroup :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [hquasisimple.1] at hderived
    exact top_unique hderived

theorem normal_le_center_of_ne_top {G : Type*} [Group G]
    (hquasisimple : IsQuasisimple G) (subgroup : Subgroup G) [subgroup.Normal]
    (hproper : subgroup ≠ ⊤) : subgroup ≤ Subgroup.center G :=
  (normal_le_center_or_eq_top hquasisimple subgroup).resolve_right hproper

theorem subnormal_le_center_or_eq_top {G : Type*} [Group G]
    (hquasisimple : IsQuasisimple G) (subgroup : Subgroup G)
    (hsubnormal : IsSubnormal subgroup ⊤) :
    subgroup ≤ Subgroup.center G ∨ subgroup = ⊤ := by
  have hchain := Components.mathlib_subnormal_of_chain hsubnormal Subgroup.IsSubnormal.top
  rcases hchain.lt_normal with htop | ⟨overgroup, hnormal, hle, hproper⟩
  · exact Or.inr htop
  · let : overgroup.Normal := hnormal
    exact Or.inl (hle.trans
      (normal_le_center_of_ne_top hquasisimple overgroup (ne_of_lt hproper)))

theorem perfect_le_center_eq_bot {G : Type*} [Group G] (subgroup : Subgroup G)
    [Group.IsPerfect subgroup] (hcentral : subgroup ≤ Subgroup.center G) :
    subgroup = ⊥ := by
  let : IsMulCommutative subgroup := isMulCommutative_iff.mpr fun left right =>
    Subtype.ext ((Subgroup.mem_center_iff.mp (hcentral left.property)) right).symm
  exact subgroup.eq_bot_of_subsingleton

theorem perfect_subnormal_eq_bot_or_eq_top {G : Type*} [Group G]
    (hquasisimple : IsQuasisimple G) (subgroup : Subgroup G)
    (hsubnormal : IsSubnormal subgroup ⊤) [Group.IsPerfect subgroup] :
    subgroup = ⊥ ∨ subgroup = ⊤ := by
  rcases subnormal_le_center_or_eq_top hquasisimple subgroup hsubnormal with hcenter | htop
  · exact Or.inl (perfect_le_center_eq_bot subgroup hcenter)
  · exact Or.inr htop

theorem perfect_subnormal_quasisimple {G : Type*} [Group G]
    (hquasisimple : IsQuasisimple G) (subgroup : Subgroup G)
    (hsubnormal : IsSubnormal subgroup ⊤) [Group.IsPerfect subgroup]
    (hne : subgroup ≠ ⊥) : IsQuasisimple subgroup := by
  have htop := (perfect_subnormal_eq_bot_or_eq_top hquasisimple subgroup hsubnormal).resolve_left hne
  exact Components.quasisimple_of_equiv
    ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv) hquasisimple

theorem perfect_double_commutator {G : Type*} [Group G]
    (perfectSubgroup otherSubgroup : Subgroup G) [Group.IsPerfect perfectSubgroup]
    (hdouble : ⁅⁅perfectSubgroup, otherSubgroup⁆, perfectSubgroup⁆ = ⊥) :
    ⁅perfectSubgroup, otherSubgroup⁆ = ⊥ := by
  have hrotate : ⁅⁅otherSubgroup, perfectSubgroup⁆, perfectSubgroup⁆ = ⊥ := by
    rwa [Subgroup.commutator_comm otherSubgroup perfectSubgroup]
  have hderived := Subgroup.commutator_commutator_eq_bot_of_rotate hdouble hrotate
  rwa [Subgroup.commutator_eq_self] at hderived

theorem center_comap_of_central_kernel {G H : Type*} [Group G] [Group H]
    [Group.IsPerfect G] (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hcentralKernel : quotient.ker ≤ Subgroup.center G) :
    (Subgroup.center H).comap quotient = Subgroup.center G := by
  apply le_antisymm
  · let preimage := (Subgroup.center H).comap quotient
    have hmap : (⁅(⊤ : Subgroup G), preimage⁆).map quotient = ⊥ := by
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective quotient hsurjective]
      change ⁅⊤, ((Subgroup.center H).comap quotient).map quotient⁆ = ⊥
      rw [Subgroup.map_comap_eq_self_of_surjective hsurjective]
      exact Subgroup.commutator_top_left_eq_bot_iff_le_center.mpr le_rfl
    have hdisplacement : ⁅(⊤ : Subgroup G), preimage⁆ ≤ Subgroup.center G :=
      ((⁅(⊤ : Subgroup G), preimage⁆).map_eq_bot_iff.mp hmap).trans hcentralKernel
    have hdouble : ⁅⁅(⊤ : Subgroup G), preimage⁆, ⊤⁆ = ⊥ :=
      Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr hdisplacement
    let : Group.IsPerfect (⊤ : Subgroup G) := Group.IsPerfect.top_iff.mpr inferInstance
    exact Subgroup.commutator_top_left_eq_bot_iff_le_center.mp
      (perfect_double_commutator ⊤ preimage hdouble)
  · intro element hcenter
    apply Subgroup.mem_center_iff.mpr
    intro other
    obtain ⟨lift, rfl⟩ := hsurjective other
    simpa only [map_mul] using congrArg quotient ((Subgroup.mem_center_iff.mp hcenter) lift)

theorem center_map_of_central_kernel {G H : Type*} [Group G] [Group H]
    [Group.IsPerfect G] (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hcentralKernel : quotient.ker ≤ Subgroup.center G) :
    (Subgroup.center G).map quotient = Subgroup.center H := by
  rw [← center_comap_of_central_kernel quotient hsurjective hcentralKernel]
  exact Subgroup.map_comap_eq_self_of_surjective hsurjective _

theorem central_quotient {G : Type*} [Group G] (hquasisimple : IsQuasisimple G)
    (centralSubgroup : Subgroup G) [centralSubgroup.Normal]
    (hcentral : centralSubgroup ≤ Subgroup.center G) :
    IsQuasisimple (G ⧸ centralSubgroup) := by
  let : Group.IsPerfect G := ⟨hquasisimple.1⟩
  let : IsSimpleGroup (G ⧸ Subgroup.center G) := hquasisimple.2
  have hcenter : (Subgroup.center G).map (QuotientGroup.mk' centralSubgroup) =
      Subgroup.center (G ⧸ centralSubgroup) :=
    center_map_of_central_kernel (QuotientGroup.mk' centralSubgroup)
      (QuotientGroup.mk'_surjective _) (by simpa only [QuotientGroup.ker_mk'] using hcentral)
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  let equivalence := QuotientGroup.quotientQuotientEquivQuotient centralSubgroup
    (Subgroup.center G) hcentral
  let centerEquivalence := QuotientGroup.congr
    ((Subgroup.center G).map (QuotientGroup.mk' centralSubgroup))
    (Subgroup.center (G ⧸ centralSubgroup)) (MulEquiv.refl _) (by simpa using hcenter)
  exact (centerEquivalence.symm.trans equivalence).isSimpleGroup

theorem nontrivial {G : Type*} [Group G] (hquasisimple : IsQuasisimple G) :
    Nontrivial G := by
  let : IsSimpleGroup (G ⧸ Subgroup.center G) := hquasisimple.2
  exact (QuotientGroup.mk'_surjective (Subgroup.center G)).nontrivial

theorem range_quasisimple_of_ker_ne_top {G H : Type*} [Group G] [Group H]
    (hquasisimple : IsQuasisimple G) (homomorphism : G →* H)
    (hkernel : homomorphism.ker ≠ ⊤) : IsQuasisimple homomorphism.range := by
  have hcentral := normal_le_center_of_ne_top hquasisimple homomorphism.ker hkernel
  exact Components.quasisimple_of_equiv
    (QuotientGroup.quotientKerEquivRange homomorphism).symm
    (central_quotient hquasisimple homomorphism.ker hcentral)

end CFSG.ComponentClassification.Quasisimple
