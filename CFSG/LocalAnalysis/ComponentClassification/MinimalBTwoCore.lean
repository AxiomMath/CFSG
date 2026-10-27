module

public import CFSG.LocalAnalysis.ComponentClassification.BFailureLocalization
public import CFSG.LocalAnalysis.ComponentClassification.LocalAmbientTwoCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.BadSolvableQuotients

public section

open CFSG.Open

namespace CFSG.ComponentClassification.MinimalBTwoCore

theorem centralizer_sup_ne_top {G : Type*} [Group G] [Finite G]
    (normalTwo twoSubgroup : Subgroup G) [normalTwo.Normal]
    (hnormalTwo : IsPGroup 2 normalTwo) (htwo : IsPGroup 2 twoSubgroup)
    (hne : normalTwo ≠ ⊥) (hoddCenter : Odd (Nat.card (Subgroup.center G))) :
    Subgroup.centralizer (normalTwo : Set G) ⊔ twoSubgroup ≠ ⊤ := by
  intro htop
  let center := (Subgroup.center normalTwo).map normalTwo.subtype
  let : center.Normal := inferInstance
  let action : twoSubgroup →* MulAut center := MulAut.conjNormal.comp twoSubgroup.subtype
  let : MulDistribMulAction twoSubgroup center := MulDistribMulAction.compHom center action
  have hcenterTwo : IsPGroup 2 center := (hnormalTwo.to_subgroup _).map normalTwo.subtype
  let : Nontrivial normalTwo := normalTwo.nontrivial_iff_ne_bot.mpr hne
  let : Nontrivial (Subgroup.center normalTwo) := hnormalTwo.center_nontrivial
  let : Nontrivial center :=
    ((Subgroup.center normalTwo).equivMapOfInjective normalTwo.subtype
      normalTwo.subtype_injective).symm.nontrivial
  have hcenterCardNe : Nat.card center ≠ 1 := by
    intro hone
    have hsubsingleton := (Nat.card_eq_one_iff_unique.mp hone).1
    obtain ⟨left, right, hneq⟩ := exists_pair_ne center
    exact hneq (hsubsingleton.elim left right)
  have htwoDivides : 2 ∣ Nat.card center := hcenterTwo.card_eq_or_dvd.resolve_left hcenterCardNe
  have honeFixed : (1 : center) ∈ MulAction.fixedPoints twoSubgroup center := by
    apply MulAction.mem_fixedPoints.mpr
    intro element
    change (action element) 1 = 1
    exact map_one _
  obtain ⟨nonidentity, hfixed, hnonidentity⟩ :=
    htwo.exists_fixed_point_of_prime_dvd_card_of_fixed_point center htwoDivides honeFixed
  have hglobalCenter : nonidentity.val ∈ Subgroup.center G := by
    apply Subgroup.mem_center_iff.mpr
    intro member
    have hcentralizer : Subgroup.centralizer (normalTwo : Set G) ≤
        Subgroup.centralizer ({nonidentity.val} : Set G) := by
      intro element helement
      apply Subgroup.mem_centralizer_iff.mpr
      intro singleton hsingleton
      rw [Set.mem_singleton_iff.mp hsingleton]
      have hnormal : nonidentity.val ∈ normalTwo := Subgroup.map_subtype_le _ nonidentity.property
      exact Subgroup.mem_centralizer_iff.mp helement nonidentity.val hnormal
    have htwoCentralizes : twoSubgroup ≤ Subgroup.centralizer ({nonidentity.val} : Set G) := by
      intro element helement
      have heq := MulAction.mem_fixedPoints.mp hfixed (⟨element, helement⟩ : twoSubgroup)
      have hvalue : element * nonidentity.val * element⁻¹ = nonidentity.val :=
        congrArg Subtype.val heq
      apply Subgroup.mem_centralizer_iff.mpr
      intro singleton hsingleton
      rw [Set.mem_singleton_iff.mp hsingleton]
      calc
        nonidentity.val * element = (element * nonidentity.val * element⁻¹) * element := by rw [hvalue]
        _ = element * nonidentity.val := by group
    have hfull := sup_le hcentralizer htwoCentralizes
    rw [htop] at hfull
    exact (Subgroup.mem_centralizer_iff.mp (hfull (Subgroup.mem_top member)) nonidentity.val
      (Set.mem_singleton nonidentity.val)).symm
  have hnontrivial : nonidentity.val ≠ 1 := by
    intro hone
    exact hnonidentity (Subtype.ext hone).symm
  have horderTwo : 2 ∣ orderOf nonidentity.val := by
    have hsubtypeNe : nonidentity ≠ 1 := fun hone => hnontrivial (congrArg Subtype.val hone)
    have hdivides := hcenterTwo.dvd_orderOf hsubtypeNe
    have horder := orderOf_injective center.subtype center.subtype_injective nonidentity
    change orderOf nonidentity.val = orderOf nonidentity at horder
    rw [horder]
    exact hdivides
  have hoddOrder : Odd (orderOf nonidentity.val) := hoddCenter.of_dvd_nat
    ((Subgroup.center G).orderOf_dvd_natCard hglobalCenter)
  exact hoddOrder.not_two_dvd_nat horderTwo

theorem normal_two_eq_bot {G : Type*} [Group G] [Finite G]
    (hoddCenter : Odd (Nat.card (Subgroup.center G)))
    (hproper : ∀ subgroup : Subgroup G, subgroup ≠ ⊤ → CentralTwoBInclusion.Property subgroup)
    (hfailure : ¬ CentralTwoBInclusion.Property G)
    (normalTwo : Subgroup G) [normalTwo.Normal] (hnormalTwo : IsPGroup 2 normalTwo) :
    normalTwo = ⊥ := by
  classical
  by_contra hne
  have hexists : ∃ twoSubgroup : Subgroup G, twoSubgroup ≠ ⊥ ∧ IsPGroup 2 twoSubgroup ∧
      ¬ (TwoComponents.badSubgroup (Subgroup.normalizer (twoSubgroup : Set G))).map
        (Subgroup.normalizer (twoSubgroup : Set G)).subtype ≤ TwoComponents.badSubgroup G := by
    by_contra hnone
    apply hfailure
    intro twoSubgroup htwoNe htwo
    by_contra hbad
    exact hnone ⟨twoSubgroup, htwoNe, htwo, hbad⟩
  obtain ⟨twoSubgroup, htwoNe, htwo, hbad⟩ := hexists
  let centralizer := Subgroup.centralizer (normalTwo : Set G)
  let overgroup := centralizer ⊔ twoSubgroup
  have hovergroupProper : overgroup ≠ ⊤ := centralizer_sup_ne_top normalTwo twoSubgroup
    hnormalTwo htwo hne hoddCenter
  have hB := hproper overgroup hovergroupProper
  have htwoLe : twoSubgroup ≤ overgroup := le_sup_right
  let normalizer := Subgroup.normalizer (twoSubgroup : Set G)
  have hbadIntersection : (TwoComponents.badSubgroup normalizer).map normalizer.subtype ≤
      (TwoComponents.badSubgroup (normalizer ⊓ overgroup : Subgroup G)).map
        (normalizer ⊓ overgroup).subtype := by
    rw [BadComponents.ambient_description, BadComponents.ambient_description]
    apply sSup_le
    rintro component ⟨hle, hcomponent, hnotQuasisimple⟩
    have hcentralizes : component ≤ centralizer := by
      have hlocal := LocalAmbientTwoCentralizers.component_le_centralizer twoSubgroup normalTwo
        htwo hnormalTwo (component.subgroupOf normalizer) hcomponent
      rwa [Subgroup.map_subgroupOf_eq_of_le hle] at hlocal
    have hintersectionLe : component ≤ normalizer ⊓ overgroup :=
      le_inf hle (hcentralizes.trans le_sup_left)
    exact le_sSup ⟨hintersectionLe, TwoComponentTransport.restrict_nested component
      (normalizer ⊓ overgroup) normalizer hintersectionLe inf_le_left hcomponent, hnotQuasisimple⟩
  have hbadOvergroup := BFailureLocalization.bad_normalizer_le_overgroup twoSubgroup overgroup
    htwo htwoLe htwoNe hB hbadIntersection
  have hbadCentralizer := BadSolvableQuotients.bad_sup_normal_two centralizer twoSubgroup htwo
  have hcentralizerSubnormal : IsSubnormal centralizer ⊤ :=
    Components.chain_of_mathlib_subnormal
      (Subgroup.IsSubnormal.step centralizer ⊤ le_top Subgroup.IsSubnormal.top inferInstance)
  exact hbad (hbadOvergroup.trans (hbadCentralizer.trans
    (BadComponentDetection.subnormal_monotone centralizer hcentralizerSubnormal)))

end CFSG.ComponentClassification.MinimalBTwoCore
