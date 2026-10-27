module

public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.ComponentClassification.QuasisimpleNormalizerCommutator

theorem eq_factor {G : Type*} [Group G] (factor : Subgroup G)
    (hquasisimple : IsQuasisimple factor) (actor : G)
    (hnormalizes : actor ∈ Subgroup.normalizer (factor : Set G))
    (hnotCentralizes : actor ∉ Subgroup.centralizer (factor : Set G)) :
    ⁅factor, Subgroup.zpowers actor⁆ = factor := by
  let generated := ⁅factor, Subgroup.zpowers actor⁆
  have hgeneratedLe : generated ≤ factor := by
    apply Subgroup.commutator_le.mpr
    intro member hmember element helement
    have helementNormalizer : element ∈ Subgroup.normalizer (factor : Set G) :=
      (Subgroup.zpowers_le.mpr hnormalizes) helement
    have hconjugate : element * member⁻¹ * element⁻¹ ∈ factor :=
      (Subgroup.mem_normalizer_iff.mp helementNormalizer member⁻¹).mp (factor.inv_mem hmember)
    change member * element * member⁻¹ * element⁻¹ ∈ factor
    simpa only [mul_assoc] using factor.mul_mem hmember hconjugate
  let localGenerated := generated.subgroupOf factor
  let : localGenerated.Normal := Subgroup.normal_subgroupOf_of_le_normalizer
    (Subgroup.normalizer_commutator_ge_left factor (Subgroup.zpowers actor))
  rcases Quasisimple.normal_le_center_or_eq_top hquasisimple localGenerated with hcentral | htop
  · let : Group.IsPerfect factor := ⟨hquasisimple.1⟩
    let localAutomorphism : MulAut factor :=
      (MulAut.conj actor).subgroupMap factor |>.trans
        (MulEquiv.subgroupCongr (by
          apply le_antisymm
          · rintro member ⟨original, horiginal, rfl⟩
            exact (Subgroup.mem_normalizer_iff.mp hnormalizes original).mp horiginal
          · intro member hmember
            have hpreimage : (MulAut.conj actor).symm member ∈ factor :=
              (Subgroup.mem_normalizer_iff''.mp hnormalizes member).mp hmember
            exact ⟨(MulAut.conj actor).symm member, hpreimage, (MulAut.conj actor).apply_symm_apply member⟩))
    have hdisplacement : ∀ member : factor, member⁻¹ * localAutomorphism member ∈ Subgroup.center factor := by
      intro member
      apply hcentral
      change member.val⁻¹ * (actor * member.val * actor⁻¹) ∈ generated
      have hcommutator := Subgroup.commutator_mem_commutator
        (factor.inv_mem member.property) (Subgroup.mem_zpowers actor)
      change member.val⁻¹ * actor * (member.val⁻¹)⁻¹ * actor⁻¹ ∈ generated at hcommutator
      simpa only [inv_inv, mul_assoc] using hcommutator
    have htrivial := PerfectAutomorphisms.hom_eq_id_of_central_displacement localAutomorphism.toMonoidHom hdisplacement
    apply False.elim
    apply hnotCentralizes
    apply Subgroup.mem_centralizer_iff.mpr
    intro member hmember
    have hfixed := congrArg (fun homomorphism : factor →* factor =>
      (homomorphism ⟨member, hmember⟩).val) htrivial
    change actor * member * actor⁻¹ = member at hfixed
    calc
      member * actor = (actor * member * actor⁻¹) * actor := by rw [hfixed]
      _ = actor * member := by group
  · have hmap := congrArg (Subgroup.map factor.subtype) htop
    rwa [Subgroup.map_subgroupOf_eq_of_le hgeneratedLe, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at hmap

end CFSG.ComponentClassification.QuasisimpleNormalizerCommutator
