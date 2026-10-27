module

public import CFSG.LocalAnalysis.ComponentClassification.TwoActionOddIntersection
public import CFSG.LocalAnalysis.ComponentClassification.SubgroupOddCoreNormalizer
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow

public section

open CFSG.Open

namespace CFSG.ComponentClassification.TwoActionSylowChoices

theorem centralizes {G : Type*} [Group G] [Finite G] (acting intersection fixed : Subgroup G)
    (hfixed : fixed ≤ intersection) (htwo : IsPGroup 2 fixed)
    (hnormalizes : acting ≤ Subgroup.normalizer (fixed : Set G))
    (hcommutator : ⁅acting, intersection⁆ ≤
      (componentClassificationOddCore intersection).map intersection.subtype) :
    ⁅acting, fixed⁆ = ⊥ := by
  have hle : ⁅acting, fixed⁆ ≤ fixed := by
    apply Subgroup.commutator_le.mpr
    intro actor hactor member hmember
    rw [commutatorElement_def]
    exact fixed.mul_mem ((Subgroup.mem_normalizer_iff.mp (hnormalizes hactor) member).mp hmember)
      (fixed.inv_mem hmember)
  have hodd : Odd (Nat.card ((componentClassificationOddCore intersection).map intersection.subtype)) := by
    rw [Subgroup.card_map_of_injective intersection.subtype_injective]
    exact OddCore.odd_card intersection
  exact TwoActionOddIntersection.two_in_odd_eq_bot ⁅acting, fixed⁆
    ((componentClassificationOddCore intersection).map intersection.subtype) (htwo.to_le hle) hodd
      ((Subgroup.commutator_mono le_rfl hfixed).trans hcommutator)

theorem extend {G : Type*} [Group G] [Finite G] (ambient acting : Subgroup G)
    (htwo : IsPGroup 2 acting)
    (hnormalizes : acting ≤ Subgroup.normalizer (ambient : Set G))
    (contained : Subgroup ambient) (hcontainedTwo : IsPGroup 2 contained)
    (hcontainedNormalizes : acting ≤ Subgroup.normalizer
      (((contained.map ambient.subtype : Subgroup G) : Set G))) :
    ∃ sylow : Sylow 2 ambient, contained ≤ sylow ∧
      acting ≤ Subgroup.normalizer ((((sylow : Subgroup ambient).map ambient.subtype : Subgroup G) : Set G)) := by
  let image := contained.map ambient.subtype
  let product := ambient ⊔ acting
  let twoProduct := image ⊔ acting
  have himage : image ≤ ambient := by
    rintro member ⟨lift, hlift, rfl⟩
    exact lift.property
  have himageTwo : IsPGroup 2 image := hcontainedTwo.map ambient.subtype
  have hproductTwo : IsPGroup 2 twoProduct :=
    himageTwo.to_sup_of_normal_left' htwo hcontainedNormalizes
  have hproductLe : twoProduct ≤ product := sup_le (himage.trans le_sup_left) le_sup_right
  obtain ⟨sylow, hsylow⟩ := (hproductTwo.comap_subtype (K := product)).exists_le_sylow
  let imageSylow : Subgroup G := (sylow : Subgroup product).map product.subtype
  have himageSylow : imageSylow ≤ product := by
    rintro member ⟨lift, hlift, rfl⟩
    exact lift.property
  have htwoProductSylow : twoProduct ≤ imageSylow := by
    have hmap := Subgroup.map_mono (f := product.subtype) hsylow
    change (twoProduct.subgroupOf product).map product.subtype ≤ imageSylow at hmap
    rw [Subgroup.map_subgroupOf_eq_of_le hproductLe] at hmap
    exact hmap
  have hactingSylow : acting ≤ imageSylow := le_sup_right.trans htwoProductSylow
  let localAmbient := ambient.subgroupOf product
  let : localAmbient.Normal := Subgroup.normal_subgroupOf_of_le_normalizer
    (sup_le Subgroup.le_normalizer hnormalizes)
  let ambientAction := localAmbient.normalizerMonoidHom.comp
    (Subgroup.inclusion (show (sylow : Subgroup product) ≤ Subgroup.normalizer (localAmbient : Set product) from
      Subgroup.le_normalizer_of_normal))
  obtain ⟨insideSylow, hinsideInvariant⟩ := TwoActionInvariantSylow.exists_invariant sylow.isPGroup' ambientAction
  let localImage : Subgroup product := (insideSylow : Subgroup localAmbient).map localAmbient.subtype
  have hlocalTwo : IsPGroup 2 localImage := insideSylow.isPGroup'.map localAmbient.subtype
  have hlocalNormalizes : (sylow : Subgroup product) ≤ Subgroup.normalizer (localImage : Set product) := by
    intro actor hactor
    apply (CommutingComponentFamily.normalizer_iff_conjugate_eq _ actor).mpr
    have hmap := congrArg (Subgroup.map localAmbient.subtype) (hinsideInvariant (⟨actor, hactor⟩ : (sylow : Subgroup product)))
    rw [Subgroup.map_map]
    rw [Subgroup.map_map] at hmap
    convert hmap using 1
    congr 1
  have hlocalInSylow : localImage ≤ sylow := by
    have htwoJoin := hlocalTwo.to_sup_of_normal_left' sylow.isPGroup' hlocalNormalizes
    have heq := sylow.is_maximal' htwoJoin (le_sup_right : (sylow : Subgroup product) ≤ localImage ⊔ sylow)
    rw [← heq]
    exact le_sup_left
  have hlocalIntersection : localImage = (sylow : Subgroup product) ⊓ localAmbient := by
    have hle : localImage ≤ localAmbient := by
      rintro member ⟨lift, hlift, rfl⟩
      exact lift.property
    apply le_antisymm (le_inf hlocalInSylow hle)
    have hotherTwo : IsPGroup 2 (((sylow : Subgroup product).subgroupOf localAmbient) : Subgroup localAmbient) :=
      sylow.isPGroup'.comap_subtype
    have hinsideLe : (insideSylow : Subgroup localAmbient) ≤ (sylow : Subgroup product).subgroupOf localAmbient := by
      intro member hmember
      exact hlocalInSylow (Subgroup.mem_map.mpr ⟨member, hmember, rfl⟩)
    have heq := insideSylow.is_maximal' hotherTwo hinsideLe
    intro member hmember
    apply Subgroup.mem_map.mpr
    refine ⟨⟨member, hmember.2⟩, ?_, rfl⟩
    rw [← heq]
    exact hmember.1
  let equivalence : localAmbient ≃* ambient := Subgroup.subgroupOfEquivOfLe (le_sup_left : ambient ≤ product)
  have hsurjective : Function.Surjective equivalence.toMonoidHom := by
    intro member
    exact ⟨equivalence.symm member, equivalence.apply_symm_apply member⟩
  let resultSylow : Sylow 2 ambient := Sylow.mapSurjective
    (f := equivalence.toMonoidHom) hsurjective insideSylow
  have hresult : (resultSylow : Subgroup ambient).map ambient.subtype = localImage.map product.subtype := by
    change ((Sylow.mapSurjective (f := equivalence.toMonoidHom) hsurjective insideSylow :
      Sylow 2 ambient) : Subgroup ambient).map ambient.subtype =
        ((insideSylow : Subgroup localAmbient).map localAmbient.subtype).map product.subtype
    rw [Sylow.coe_mapSurjective (f := equivalence.toMonoidHom) hsurjective insideSylow,
      Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hambientIntersection : (resultSylow : Subgroup ambient).map ambient.subtype = imageSylow ⊓ ambient := by
    rw [hresult, hlocalIntersection, Subgroup.map_inf _ _ _ product.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le (le_sup_left : ambient ≤ product)]
  refine ⟨resultSylow, ?_, ?_⟩
  · intro member hmember
    have hmem : member.val ∈ (resultSylow : Subgroup ambient).map ambient.subtype := by
      rw [hambientIntersection]
      exact ⟨htwoProductSylow ((le_sup_left : image ≤ twoProduct)
        (Subgroup.mem_map.mpr ⟨member, hmember, rfl⟩)), member.property⟩
    obtain ⟨lift, hlift, heq⟩ := Subgroup.mem_map.mp hmem
    have hequal : lift = member := Subtype.ext heq
    exact hequal ▸ hlift
  · rw [hambientIntersection]
    exact SubgroupOddCoreNormalizer.inf imageSylow ambient acting
      (hactingSylow.trans Subgroup.le_normalizer) hnormalizes

theorem choices {G : Type*} [Group G] [Finite G] (ambient acting intersection : Subgroup G)
    (hintersection : intersection ≤ ambient) (htwo : IsPGroup 2 acting)
    (hnormalizesAmbient : acting ≤ Subgroup.normalizer (ambient : Set G))
    (hnormalizesIntersection : acting ≤ Subgroup.normalizer (intersection : Set G))
    (hcommutator : ⁅acting, intersection⁆ ≤
      (componentClassificationOddCore intersection).map intersection.subtype) :
    ∃ first : Sylow 2 intersection, ∃ second : Sylow 2 ambient,
      let firstImage := (first : Subgroup intersection).map intersection.subtype
      let secondImage := (second : Subgroup ambient).map ambient.subtype
      firstImage ≤ secondImage ∧ intersection ⊓ secondImage = firstImage ∧
        acting ≤ Subgroup.normalizer (secondImage : Set G) ∧ ⁅acting, firstImage⁆ = ⊥ := by
  obtain ⟨first, hfirstNormalizes⟩ := TwoActionInvariantSylow.subgroup intersection acting htwo hnormalizesIntersection
  let firstImage := (first : Subgroup intersection).map intersection.subtype
  have hfirstImage : firstImage ≤ intersection := by
    rintro member ⟨lift, hlift, rfl⟩
    exact lift.property
  have hfirstAmbient := hfirstImage.trans hintersection
  have hfirstTwo : IsPGroup 2 firstImage := first.isPGroup'.map intersection.subtype
  have hfirstCore := centralizes acting intersection firstImage hfirstImage hfirstTwo hfirstNormalizes hcommutator
  obtain ⟨second, hcontained, hsecondNormalizes⟩ := extend ambient acting htwo hnormalizesAmbient
    (firstImage.subgroupOf ambient) (hfirstTwo.comap_subtype (K := ambient)) (by
      rw [Subgroup.map_subgroupOf_eq_of_le hfirstAmbient]
      exact hfirstNormalizes)
  let secondImage := (second : Subgroup ambient).map ambient.subtype
  have hfirstSecond : firstImage ≤ secondImage := by
    have hmap := Subgroup.map_mono (f := ambient.subtype) hcontained
    rw [Subgroup.map_subgroupOf_eq_of_le hfirstAmbient] at hmap
    exact hmap
  refine ⟨first, second, hfirstSecond, ?_, hsecondNormalizes, hfirstCore⟩
  have hsecondTwo : IsPGroup 2 secondImage := second.isPGroup'.map ambient.subtype
  have hlocalTwo : IsPGroup 2 (secondImage.subgroupOf intersection) := hsecondTwo.comap_subtype
  have hfirstLe : (first : Subgroup intersection) ≤ secondImage.subgroupOf intersection := by
    intro member hmember
    exact hfirstSecond (Subgroup.mem_map.mpr ⟨member, hmember, rfl⟩)
  have heq := first.is_maximal' hlocalTwo hfirstLe
  apply le_antisymm _ (le_inf hfirstImage hfirstSecond)
  intro member hmember
  apply Subgroup.mem_map.mpr
  refine ⟨⟨member, hmember.1⟩, ?_, rfl⟩
  rw [← heq]
  exact hmember.2

end CFSG.ComponentClassification.TwoActionSylowChoices
