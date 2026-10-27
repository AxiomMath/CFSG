module

public import CFSG.LocalAnalysis.ComponentClassification.CentralTwoBInclusion

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BFailureLocalization

theorem bad_normalizer_le_intersection {G : Type*} [Group G] [Finite G]
    (twoSubgroup : Subgroup G) (htwo : IsPGroup 2 twoSubgroup) (element : G)
    (helement : element ∈ twoSubgroup) :
    (TwoComponents.badSubgroup (Subgroup.normalizer (twoSubgroup : Set G))).map
        (Subgroup.normalizer (twoSubgroup : Set G)).subtype ≤
      (TwoComponents.badSubgroup
        (Subgroup.normalizer (twoSubgroup : Set G) ⊓
          Subgroup.centralizer ({element} : Set G) : Subgroup G)).map
          (Subgroup.normalizer (twoSubgroup : Set G) ⊓
            Subgroup.centralizer ({element} : Set G)).subtype := by
  let normalizer := Subgroup.normalizer (twoSubgroup : Set G)
  let centralizer := Subgroup.centralizer ({element} : Set G)
  let intersection := normalizer ⊓ centralizer
  rw [BadComponents.ambient_description, BadComponents.ambient_description]
  apply sSup_le
  rintro component ⟨hle, hcomponent, hnotQuasisimple⟩
  have hcentralizes := TwoComponentCentralizers.le_ambient_centralizer component twoSubgroup
    normalizer hle Subgroup.le_normalizer le_rfl hcomponent htwo
  have hcentralizerLe : component ≤ centralizer := by
    intro member hmem
    apply Subgroup.mem_centralizer_iff.mpr
    intro singleton hsingleton
    rw [Set.mem_singleton_iff.mp hsingleton]
    exact Subgroup.mem_centralizer_iff.mp (hcentralizes hmem) element helement
  have hintersectionLe : component ≤ intersection := le_inf hle hcentralizerLe
  exact le_sSup ⟨hintersectionLe,
    TwoComponentTransport.restrict_nested component intersection normalizer hintersectionLe
      inf_le_left hcomponent, hnotQuasisimple⟩

theorem bad_normalizer_le_overgroup {G : Type*} [Group G] [Finite G]
    (twoSubgroup overgroup : Subgroup G) (htwo : IsPGroup 2 twoSubgroup)
    (htwoLe : twoSubgroup ≤ overgroup) (hne : twoSubgroup ≠ ⊥)
    (hB : CentralTwoBInclusion.Property overgroup)
    (hbadContained : (TwoComponents.badSubgroup
      (Subgroup.normalizer (twoSubgroup : Set G))).map
        (Subgroup.normalizer (twoSubgroup : Set G)).subtype ≤
          (TwoComponents.badSubgroup
            (Subgroup.normalizer (twoSubgroup : Set G) ⊓ overgroup : Subgroup G)).map
            (Subgroup.normalizer (twoSubgroup : Set G) ⊓ overgroup).subtype) :
    (TwoComponents.badSubgroup (Subgroup.normalizer (twoSubgroup : Set G))).map
        (Subgroup.normalizer (twoSubgroup : Set G)).subtype ≤
      (TwoComponents.badSubgroup overgroup).map overgroup.subtype := by
  let normalizer := Subgroup.normalizer (twoSubgroup : Set G)
  let intersection := normalizer ⊓ overgroup
  let localTwo := twoSubgroup.subgroupOf overgroup
  let localNormalizer := Subgroup.normalizer (localTwo : Set overgroup)
  have hlocalNe : localTwo ≠ ⊥ := by
    intro hbot
    have hmap := congrArg (Subgroup.map overgroup.subtype) hbot
    rw [Subgroup.map_subgroupOf_eq_of_le htwoLe, Subgroup.map_bot] at hmap
    exact hne hmap
  have hlocalB := hB localTwo hlocalNe htwo.comap_subtype
  have hnormalizerEq : localNormalizer = normalizer.subgroupOf overgroup :=
    (Subgroup.subgroupOf_normalizer_eq htwoLe).symm
  have hnormalizerMap : localNormalizer.map overgroup.subtype = intersection := by
    rw [hnormalizerEq, Subgroup.subgroupOf_map_subtype]
  let equivalence :=
    (localNormalizer.equivMapOfInjective overgroup.subtype overgroup.subtype_injective).trans
      (MulEquiv.subgroupCongr hnormalizerMap)
  have hbadMap : ((TwoComponents.badSubgroup localNormalizer).map localNormalizer.subtype).map
      overgroup.subtype = (TwoComponents.badSubgroup intersection).map intersection.subtype := by
    have hinvariant := BadComponents.equiv_invariant equivalence
    have hcomposite : overgroup.subtype.comp localNormalizer.subtype =
        intersection.subtype.comp equivalence.toMonoidHom := rfl
    rw [Subgroup.map_map, hcomposite, ← Subgroup.map_map, hinvariant]
  have hlocalImage := Subgroup.map_mono (f := overgroup.subtype) hlocalB
  rw [hbadMap] at hlocalImage
  exact hbadContained.trans hlocalImage

theorem bad_normalizer_le_centralizer {G : Type*} [Group G] [Finite G]
    (twoSubgroup : Subgroup G) (htwo : IsPGroup 2 twoSubgroup) (hne : twoSubgroup ≠ ⊥)
    (element : G) (helement : element ∈ twoSubgroup)
    (hcentral : ∀ member ∈ twoSubgroup, element * member = member * element)
    (hB : CentralTwoBInclusion.Property (Subgroup.centralizer ({element} : Set G))) :
    (TwoComponents.badSubgroup (Subgroup.normalizer (twoSubgroup : Set G))).map
        (Subgroup.normalizer (twoSubgroup : Set G)).subtype ≤
      (TwoComponents.badSubgroup (Subgroup.centralizer ({element} : Set G))).map
        (Subgroup.centralizer ({element} : Set G)).subtype := by
  have htwoLe : twoSubgroup ≤ Subgroup.centralizer ({element} : Set G) := by
    intro member hmem
    apply Subgroup.mem_centralizer_iff.mpr
    intro singleton hsingleton
    rw [Set.mem_singleton_iff.mp hsingleton]
    exact hcentral member hmem
  exact bad_normalizer_le_overgroup twoSubgroup _ htwo htwoLe hne hB
    (bad_normalizer_le_intersection twoSubgroup htwo element helement)

theorem centralizer_proper_of_odd_center {G : Type*} [Group G] [Finite G]
    (hoddCenter : Odd (Nat.card (Subgroup.center G))) (involution : G)
    (hinvolution : orderOf involution = 2) :
    Subgroup.centralizer ({involution} : Set G) ≠ ⊤ := by
  intro htop
  have hcenter : involution ∈ Subgroup.center G := by
    apply Subgroup.mem_center_iff.mpr
    intro member
    have hcentralizer : member ∈ Subgroup.centralizer ({involution} : Set G) := by
      rw [htop]
      exact Subgroup.mem_top _
    exact (Subgroup.mem_centralizer_iff.mp hcentralizer involution
      (Set.mem_singleton involution)).symm
  have hcyclic : Subgroup.zpowers involution ≤ Subgroup.center G := Subgroup.zpowers_le.mpr hcenter
  have hoddCyclic := hoddCenter.of_dvd_nat (Subgroup.card_dvd_of_le hcyclic)
  rw [Nat.card_zpowers, hinvolution] at hoddCyclic
  exact (by decide : ¬ Odd 2) hoddCyclic

theorem centralizer_failure {G : Type*} [Group G] [Finite G]
    (hoddCenter : Odd (Nat.card (Subgroup.center G)))
    (hproper : ∀ subgroup : Subgroup G, subgroup ≠ ⊤ → CentralTwoBInclusion.Property subgroup)
    (twoSubgroup : Subgroup G) (htwo : IsPGroup 2 twoSubgroup) (hne : twoSubgroup ≠ ⊥)
    (hfailure : ¬ (TwoComponents.badSubgroup (Subgroup.normalizer (twoSubgroup : Set G))).map
      (Subgroup.normalizer (twoSubgroup : Set G)).subtype ≤ TwoComponents.badSubgroup G)
    (involution : G) (hinvolution : orderOf involution = 2) (hinSubgroup : involution ∈ twoSubgroup)
    (hcentral : ∀ member ∈ twoSubgroup, involution * member = member * involution) :
    Subgroup.centralizer ({involution} : Set G) ≠ ⊤ ∧
      ¬ (TwoComponents.badSubgroup (Subgroup.centralizer ({involution} : Set G))).map
        (Subgroup.centralizer ({involution} : Set G)).subtype ≤ TwoComponents.badSubgroup G := by
  have hneTop := centralizer_proper_of_odd_center hoddCenter involution hinvolution
  refine ⟨hneTop, ?_⟩
  intro hcontained
  exact hfailure ((bad_normalizer_le_centralizer twoSubgroup htwo hne involution hinSubgroup
    hcentral (hproper _ hneTop)).trans hcontained)

theorem exists_central_involution {G : Type*} [Group G] [Finite G]
    (twoSubgroup : Subgroup G) (htwo : IsPGroup 2 twoSubgroup) (hne : twoSubgroup ≠ ⊥) :
    ∃ involution : G, orderOf involution = 2 ∧ involution ∈ twoSubgroup ∧
      ∀ member ∈ twoSubgroup, involution * member = member * involution := by
  let : Nontrivial twoSubgroup := twoSubgroup.nontrivial_iff_ne_bot.mpr hne
  let : Nontrivial (Subgroup.center twoSubgroup) := htwo.center_nontrivial
  have hcenterTwo : IsPGroup 2 (Subgroup.center twoSubgroup) := htwo.to_subgroup _
  have hcardNe : Nat.card (Subgroup.center twoSubgroup) ≠ 1 := by
    intro hone
    obtain ⟨left, right, hneq⟩ := exists_pair_ne (Subgroup.center twoSubgroup)
    exact hneq ((Nat.card_eq_one_iff_unique.mp hone).1.elim left right)
  have hdivides : 2 ∣ Nat.card (Subgroup.center twoSubgroup) :=
    hcenterTwo.card_eq_or_dvd.resolve_left hcardNe
  obtain ⟨element, horder⟩ := exists_prime_orderOf_dvd_card' 2 hdivides
  have horderCenter := orderOf_injective (Subgroup.center twoSubgroup).subtype
    (Subgroup.center twoSubgroup).subtype_injective element
  have horderAmbient := orderOf_injective twoSubgroup.subtype twoSubgroup.subtype_injective element.val
  refine ⟨element.val.val, horderAmbient.trans (horderCenter.trans horder), element.val.property, ?_⟩
  intro member hmember
  exact congrArg (fun value : twoSubgroup => (value : G))
    (Subgroup.mem_center_iff.mp element.property (⟨member, hmember⟩ : twoSubgroup)).symm

theorem exists_involution_centralizer_failure {G : Type*} [Group G] [Finite G]
    (hoddCenter : Odd (Nat.card (Subgroup.center G)))
    (hproper : ∀ subgroup : Subgroup G, subgroup ≠ ⊤ → CentralTwoBInclusion.Property subgroup)
    (hfailure : ¬ CentralTwoBInclusion.Property G) :
    ∃ involution : G, orderOf involution = 2 ∧
      Subgroup.centralizer ({involution} : Set G) ≠ ⊤ ∧
      ¬ (TwoComponents.badSubgroup (Subgroup.centralizer ({involution} : Set G))).map
        (Subgroup.centralizer ({involution} : Set G)).subtype ≤ TwoComponents.badSubgroup G := by
  classical
  obtain ⟨twoSubgroup, hne, htwo, hlocalFailure⟩ :
      ∃ twoSubgroup : Subgroup G, twoSubgroup ≠ ⊥ ∧ IsPGroup 2 twoSubgroup ∧
        ¬ (TwoComponents.badSubgroup (Subgroup.normalizer (twoSubgroup : Set G))).map
          (Subgroup.normalizer (twoSubgroup : Set G)).subtype ≤ TwoComponents.badSubgroup G := by
    by_contra hnone
    apply hfailure
    intro twoSubgroup hne htwo
    by_contra hlocalFailure
    exact hnone ⟨twoSubgroup, hne, htwo, hlocalFailure⟩
  obtain ⟨involution, horder, hmem, hcentral⟩ := exists_central_involution twoSubgroup htwo hne
  exact ⟨involution, horder, centralizer_failure hoddCenter hproper twoSubgroup htwo hne
    hlocalFailure involution horder hmem hcentral⟩

end CFSG.ComponentClassification.BFailureLocalization
