module

public import CFSG.LocalAnalysis.ComponentClassification.BlockProductFusion

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockTwoActionFaithful

theorem action_injective {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (first second third : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (hthird : third ∈ UniversalOrbitBlock.block component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (twoSubgroup : Subgroup G) (htwo : IsPGroup 2 twoSubgroup)
    (hcontained : twoSubgroup ≤ UniversalOrbitBlock.conjugate second actor ⊔ UniversalOrbitBlock.conjugate third actor)
    (hnormalizes : twoSubgroup ≤ Subgroup.normalizer (first : Set G)) :
    Function.Injective (first.normalizerMonoidHom.comp (Subgroup.inclusion hnormalizes)) := by
  let action := first.normalizerMonoidHom.comp (Subgroup.inclusion hnormalizes)
  have hkernelTwo : IsPGroup 2 action.ker := htwo.to_subgroup action.ker
  have hkernelCard : Nat.card action.ker = 1 := by
    rcases hkernelTwo.card_eq_or_dvd with hone | hdivides
    · exact hone
    · obtain ⟨member, horder⟩ := exists_prime_orderOf_dvd_card' (G := action.ker) 2 hdivides
      have hambientOrder : orderOf member.val.val = 2 :=
        ((orderOf_injective twoSubgroup.subtype twoSubgroup.subtype_injective member.val).trans
          (orderOf_injective action.ker.subtype action.ker.subtype_injective member)).trans horder
      have hcentralizes : member.val.val ∈ Subgroup.centralizer (first : Set G) := by
        have hker : Subgroup.inclusion hnormalizes member.val ∈ first.normalizerMonoidHom.ker := member.property
        rw [Subgroup.normalizerMonoidHom_ker] at hker
        exact hker
      have hbaseFusion : member.val.val ∈ BlockFusion.involutions component :=
        ⟨hambientOrder, first, hfirst, hcentralizes⟩
      have himage : member.val.val ∈ (second ⊔ third).map (MulAut.conj actor).toMonoidHom := by
        rw [Subgroup.map_sup]
        exact hcontained member.val.property
      obtain ⟨original, horiginal, heq⟩ := Subgroup.mem_map.mp himage
      have horiginalOrder : orderOf original = 2 :=
        (orderOf_injective (MulAut.conj actor).toMonoidHom (MulAut.conj actor).injective original).symm.trans
          ((congrArg orderOf heq).trans hambientOrder)
      have horiginalFusion := BlockProductFusion.product_involution_mem component heven huniversal hcard
        second third hsecond hthird original horiginal horiginalOrder
      have hnormalizesActor := (BlockFusion.transporter_iff component heven huniversal hquasisimple original
        horiginalFusion actor).mp (by
          have heq' : (MulAut.conj actor) original = member.val.val := heq
          rwa [heq'])
      exact (hactor hnormalizesActor).elim
  have hkernelBot : action.ker = ⊥ := action.ker.eq_bot_iff_card.mpr hkernelCard
  exact (MonoidHom.ker_eq_bot_iff action).mp hkernelBot

theorem center_quotient_action_injective {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (first second third : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (hthird : third ∈ UniversalOrbitBlock.block component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (twoSubgroup : Subgroup G) (htwo : IsPGroup 2 twoSubgroup)
    (hcontained : twoSubgroup ≤ UniversalOrbitBlock.conjugate second actor ⊔ UniversalOrbitBlock.conjugate third actor)
    (hnormalizes : twoSubgroup ≤ Subgroup.normalizer (first : Set G)) :
    Function.Injective ((PerfectAutomorphisms.centerQuotientHom first).comp
      (first.normalizerMonoidHom.comp (Subgroup.inclusion hnormalizes))) := by
  let : Group.IsPerfect first := ⟨(UniversalOrbitBlock.orbit_quasisimple component hquasisimple first hfirst.1).1⟩
  exact (PerfectAutomorphisms.centerQuotientHom_injective first).comp
    (action_injective component heven huniversal hquasisimple hcard first second third hfirst hsecond hthird
      actor hactor twoSubgroup htwo hcontained hnormalizes)

theorem disjoint_factor {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (first second third : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (hthird : third ∈ UniversalOrbitBlock.block component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (twoSubgroup : Subgroup G) (htwo : IsPGroup 2 twoSubgroup)
    (hcontained : twoSubgroup ≤ UniversalOrbitBlock.conjugate second actor ⊔ UniversalOrbitBlock.conjugate third actor) :
    Disjoint first twoSubgroup := by
  have hintersectionTwo : IsPGroup 2 ↥(first ⊓ twoSubgroup) := htwo.to_le inf_le_right
  have hodd : Odd (Nat.card ↥(first ⊓ twoSubgroup)) :=
    (BlockProductFusion.intersection_odd component heven huniversal hquasisimple hcard first first second third
      hfirst hfirst hsecond hthird actor hactor).of_dvd_nat
      (Subgroup.card_dvd_of_le (inf_le_inf (le_sup_left : first ≤ first ⊔ first) hcontained))
  apply disjoint_iff.mpr
  apply (first ⊓ twoSubgroup).eq_bot_iff_card.mpr
  rcases hintersectionTwo.card_eq_or_dvd with hone | hdivides
  · exact hone
  · exact (hodd.not_two_dvd_nat hdivides).elim

theorem centralizer_le_image_normalizer {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (second third : Subgroup G)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (hthird : third ∈ UniversalOrbitBlock.block component) (actor : G)
    (twoSubgroup : Subgroup G) (htwo : IsPGroup 2 twoSubgroup)
    (hcontained : twoSubgroup ≤ UniversalOrbitBlock.conjugate second actor ⊔ UniversalOrbitBlock.conjugate third actor)
    (member : G) (hmember : member ∈ twoSubgroup) (hne : member ≠ 1) :
    Subgroup.centralizer {member} ≤
      (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom := by
  have hcyclicTwo : IsPGroup 2 (Subgroup.zpowers member) :=
    htwo.to_le (Subgroup.zpowers_le.mpr hmember)
  have hcyclicNontrivial : Nontrivial (Subgroup.zpowers member) :=
    (Subgroup.zpowers member).nontrivial_iff_ne_bot.mpr (Subgroup.zpowers_ne_bot.mpr hne)
  let : Nontrivial (Subgroup.zpowers member) := hcyclicNontrivial
  have hcyclicEven : 2 ∣ Nat.card (Subgroup.zpowers member) := by
    rcases hcyclicTwo.card_eq_or_dvd with hone | hdivides
    · have hbot := (Subgroup.zpowers member).eq_bot_iff_card.mpr hone
      exact ((Subgroup.zpowers_ne_bot.mpr hne) hbot).elim
    · exact hdivides
  obtain ⟨involution, horder⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers member) 2 hcyclicEven
  have hambientOrder : orderOf involution.val = 2 :=
    (orderOf_injective (Subgroup.zpowers member).subtype (Subgroup.zpowers member).subtype_injective involution).trans horder
  have hinvolutionTwo : involution.val ∈ twoSubgroup :=
    (Subgroup.zpowers_le.mpr hmember) involution.property
  have himage : involution.val ∈ (second ⊔ third).map (MulAut.conj actor).toMonoidHom := by
    rw [Subgroup.map_sup]
    exact hcontained hinvolutionTwo
  obtain ⟨original, horiginal, heq⟩ := Subgroup.mem_map.mp himage
  have horiginalOrder : orderOf original = 2 :=
    (orderOf_injective (MulAut.conj actor).toMonoidHom (MulAut.conj actor).injective original).symm.trans
      ((congrArg orderOf heq).trans hambientOrder)
  have horiginalFusion := BlockProductFusion.product_involution_mem component heven huniversal hcard
    second third hsecond hthird original horiginal horiginalOrder
  obtain ⟨horderOriginal, other, hother, hcentralizes⟩ := horiginalFusion
  have hcentralizerImage := Subgroup.map_mono (f := (MulAut.conj actor).toMonoidHom)
    (UniversalOrbitBlock.involution_centralizer_le component heven huniversal hquasisimple other hother
      original horderOriginal hcentralizes)
  rw [UniversalComponentBlock.singleton_centralizer_map] at hcentralizerImage
  have heq' : (MulAut.conj actor) original = involution.val := heq
  rw [heq'] at hcentralizerImage
  intro central hcentral
  apply hcentralizerImage
  have hcyclicCentral : Subgroup.zpowers member ≤ Subgroup.centralizer {central} := by
    apply Subgroup.zpowers_le.mpr
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact (Subgroup.mem_centralizer_singleton_iff.mp hcentral).symm
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hcyclicCentral involution.property)).symm

end CFSG.ComponentClassification.BlockTwoActionFaithful
