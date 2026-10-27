module

public import CFSG.LocalAnalysis.ComponentClassification.InvolutionFixedPoints
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

open CFSG.Open

namespace CFSG.ComponentClassification.ComponentInvolutionWitness

theorem exists_fixed_noncentralizing {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (hcomponent : IsComponentOf component ⊤)
    (heven : 2 ∣ Nat.card component) (hcenter : Subgroup.center component = ⊥)
    (automorphism : MulAut G) (hinvolutive : Function.Involutive automorphism) :
    ∃ member : G, member ∈ component ⊔ component.map automorphism.toMonoidHom ∧
      member * member = 1 ∧ automorphism member = member ∧
      member ∉ Subgroup.centralizer (component : Set G) := by
  let partner := component.map automorphism.toMonoidHom
  have hpartner : IsComponentOf partner ⊤ :=
    (LocalComponents.equiv_iff automorphism component).mpr hcomponent
  have hnoncentralizing : ∀ member : component, member ≠ 1 →
      member.val ∉ Subgroup.centralizer (component : Set G) := by
    intro member hne hcentralizes
    have hcentral : member ∈ Subgroup.center component := by
      apply Subgroup.mem_center_iff.mpr
      intro other
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hcentralizes other.val other.property)
    rw [hcenter, Subgroup.mem_bot] at hcentral
    exact hne hcentral
  by_cases heq : partner = component
  · let restricted := (automorphism.subgroupMap component).trans (MulEquiv.subgroupCongr heq)
    have hrestricted : Function.Involutive restricted := by
      intro member
      apply Subtype.ext
      exact hinvolutive member.val
    obtain ⟨member, horder, hfixed⟩ := InvolutionFixedPoints.exists_fixed_involution heven
      restricted hrestricted
    have hne : member ≠ 1 := by intro hone; rw [hone, orderOf_one] at horder; omega
    have hsquare : member.val * member.val = 1 := by
      have hpower := pow_orderOf_eq_one member
      rw [horder, pow_two] at hpower
      exact congrArg Subtype.val hpower
    exact ⟨member.val, (le_sup_left : component ≤ component ⊔ partner) member.property,
      hsquare, congrArg Subtype.val hfixed,
      hnoncentralizing member hne⟩
  · obtain ⟨member, horder⟩ := exists_prime_orderOf_dvd_card' 2 heven
    have hne : member ≠ 1 := by intro hone; rw [hone, orderOf_one] at horder; omega
    have hsquare : member.val * member.val = 1 := by
      have hpower := pow_orderOf_eq_one member
      rw [horder, pow_two] at hpower
      exact congrArg Subtype.val hpower
    have hpartnerMem : automorphism member.val ∈ partner :=
      Subgroup.mem_map_of_mem automorphism.toMonoidHom member.property
    have hcentralizes := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (LocalComponents.commute_of_ne partner component hpartner hcomponent heq) hpartnerMem
    have hcommute : Commute member.val (automorphism member.val) :=
      Subgroup.mem_centralizer_iff.mp hcentralizes member.val member.property
    refine ⟨member.val * automorphism member.val,
      Subgroup.mul_mem_sup member.property hpartnerMem, ?_, ?_, ?_⟩
    · have hautoSquare : automorphism member.val * automorphism member.val = 1 := by
        rw [← map_mul, hsquare, map_one]
      rw [← pow_two, hcommute.mul_pow, pow_two, pow_two, hsquare, hautoSquare, one_mul]
    · rw [map_mul, hinvolutive]
      exact hcommute.eq.symm
    · intro hproductCentralizes
      have hmemberCentralizes := (Subgroup.centralizer (component : Set G)).mul_mem
        hproductCentralizes ((Subgroup.centralizer (component : Set G)).inv_mem hcentralizes)
      exact hnoncentralizing member hne (by simpa only [mul_inv_cancel_right] using hmemberCentralizes)

end CFSG.ComponentClassification.ComponentInvolutionWitness
