module

public import CFSG.LocalAnalysis.ComponentClassification.SolvableRadical
public import CFSG.LocalAnalysis.ComponentClassification.MinimalNormal
public import CFSG.LocalAnalysis.ComponentClassification.ComponentAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.ComponentInnerActions

public section

open CFSG.Open

namespace CFSG.ComponentClassification.RadicalFreeLayer

theorem simple_quasisimple {G : Type*} [Group G] [IsSimpleGroup G]
    (hfree : SolvableRadical.Free G) : IsQuasisimple G := by
  have hnonab : ∃ left right : G, left * right ≠ right * left := by
    by_contra hcommutes
    have hcommutative : IsMulCommutative G := isMulCommutative_iff.mpr
      (by intro left right; exact not_ne_iff.mp (fun hne => hcommutes ⟨left, right, hne⟩))
    let : IsMulCommutative G := hcommutative
    let : Group.IsSolvable G := Group.isSolvable_of_comm
      (fun left right => (isMulCommutative_iff.mp hcommutative) left right)
    have hbot := hfree ⊤ inferInstance inferInstance
    exact top_ne_bot hbot
  have hcenter := Helpers.center_eq_bot G hnonab
  refine ⟨Helpers.commutator_eq_top G hnonab, ?_⟩
  exact ((QuotientGroup.congr (Subgroup.center G) ⊥ (MulEquiv.refl G)
    (by
      change (Subgroup.center G).map (MonoidHom.id G) = ⊥
      rwa [Subgroup.map_id])).trans
    (QuotientGroup.quotientBot (G := G))).isSimpleGroup

theorem exists_component {G : Type*} [Group G] [Finite G]
    (hfree : SolvableRadical.Free G) [Nontrivial G] :
    ∃ component : Subgroup G, IsComponentOf component ⊤ := by
  induction hcard : Nat.card G using Nat.strong_induction_on generalizing G with
  | h cardinal hinduction =>
      obtain ⟨minimalNormal, _, hminimal⟩ := MinimalNormal.exists_le (⊤ : Subgroup G) top_ne_bot
      let : minimalNormal.Normal := hminimal.prop.1
      by_cases htop : minimalNormal = ⊤
      · have hsimple : IsSimpleGroup G := by
          apply (isSimpleGroup_iff G).mpr
          refine ⟨inferInstance, ?_⟩
          intro candidate hcandidate
          by_cases hbot : candidate = ⊥
          · exact Or.inl hbot
          · right
            have hle : candidate ≤ minimalNormal := htop ▸ le_top
            have heq := (minimal_iff.mp hminimal).2 ⟨hcandidate, hbot⟩ hle
            exact heq.symm.trans htop
        let : IsSimpleGroup G := hsimple
        exact ⟨⊤, le_rfl, .refl ⊤,
          Components.quasisimple_of_equiv Subgroup.topEquiv (simple_quasisimple hfree)⟩
      · have hsmaller : Nat.card minimalNormal < cardinal := by
          have hle := minimalNormal.card_le_card_group
          have hne : Nat.card minimalNormal ≠ Nat.card G :=
            fun heq => htop (minimalNormal.card_eq_iff_eq_top.mp heq)
          omega
        let : Nontrivial minimalNormal := minimalNormal.nontrivial_iff_ne_bot.mpr hminimal.prop.2
        obtain ⟨component, hcomponent⟩ := hinduction (Nat.card minimalNormal) hsmaller
          (SolvableRadical.free_normal_subgroup hfree minimalNormal) rfl
        exact ⟨component.map minimalNormal.subtype,
          LocalComponents.of_subnormal_subgroup minimalNormal
            (Components.chain_of_mathlib_subnormal
              (inferInstance : minimalNormal.Normal).isSubnormal) component hcomponent⟩

theorem center_eq_bot {G : Type*} [Group G] (hfree : SolvableRadical.Free G) :
    Subgroup.center G = ⊥ := by
  let : Group.IsSolvable (Subgroup.center G) := Group.isSolvable_of_comm
    (fun left right => (isMulCommutative_iff.mp inferInstance) left right)
  exact hfree (Subgroup.center G) inferInstance inferInstance

theorem layer_centralizer_eq_bot {G : Type*} [Group G] [Finite G]
    (hfree : SolvableRadical.Free G) :
    Subgroup.centralizer (Layer.subgroup G : Set G) = ⊥ := by
  let layer := Layer.subgroup G
  let : layer.Normal := Layer.normal G
  let centralizer := Subgroup.centralizer (layer : Set G)
  by_contra hne
  let : Nontrivial centralizer := centralizer.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨component, hcomponent⟩ := exists_component
    (SolvableRadical.free_normal_subgroup hfree centralizer)
  have hambient := LocalComponents.of_subnormal_subgroup centralizer
    (Components.chain_of_mathlib_subnormal (inferInstance : centralizer.Normal).isSubnormal)
    component hcomponent
  let image := component.map centralizer.subtype
  have hleLayer : image ≤ layer := Layer.component_le hambient
  have hleCentralizer : image ≤ centralizer := Subgroup.map_subtype_le _
  have hcommutative : IsMulCommutative image := by
    apply isMulCommutative_iff.mpr
    intro left right
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp
      (hleCentralizer left.property) right.val (hleLayer right.property)).symm)
  let : IsMulCommutative image := hcommutative
  let : Group.IsPerfect image := ⟨hambient.2.2.1⟩
  have hsubsingleton : Subsingleton image := inferInstance
  have hbot : image = ⊥ := by
    apply le_antisymm _ bot_le
    intro member hmember
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val
      (hsubsingleton.elim (⟨member, hmember⟩ : image) 1))
  exact (image.nontrivial_iff_ne_bot.mp (Quasisimple.nontrivial hambient.2.2)) hbot

theorem perfect_normalizer_enters_layer {G : Type*} [Group G] [Finite G]
    (hfree : SolvableRadical.Free G) (perfectSubgroup : Subgroup G)
    [Group.IsPerfect perfectSubgroup]
    (hnormalizes : ∀ component : Subgroup G, IsComponentOf component ⊤ →
      perfectSubgroup ≤ Subgroup.normalizer (component : Set G))
    (houter : ∀ component : Subgroup G, IsComponentOf component ⊤ →
      Group.IsSolvable (OuterAutomorphisms.Outer (component ⧸ Subgroup.center component))) :
    perfectSubgroup ≤ Layer.subgroup G := by
  intro actor hactor
  have hinner : ∀ component : Subgroup G, IsComponentOf component ⊤ →
      ∃ implementer ∈ component, ∀ member ∈ component,
        actor * member * actor⁻¹ = implementer * member * implementer⁻¹ := by
    intro component hcomponent
    let : Group.IsPerfect component := ⟨hcomponent.2.2.1⟩
    let : Group.IsSolvable (OuterAutomorphisms.Outer (component ⧸ Subgroup.center component)) :=
      houter component hcomponent
    let : Group.IsSolvable (OuterAutomorphisms.Outer component) :=
      OuterAutomorphisms.solvable_of_centerQuotient component
    exact ComponentInnerActions.perfect_normalizer_action_inner perfectSubgroup component
      (hnormalizes component hcomponent) (⟨actor, hactor⟩ : perfectSubgroup)
  obtain ⟨implementer, himplementer, haction⟩ :=
    ComponentInnerActions.exists_layer_implementer actor hinner
  have hcentralizer : implementer⁻¹ * actor ∈
      Subgroup.centralizer (Layer.subgroup G : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro member hmember
    have heq := congrArg (fun value : G => implementer⁻¹ * value * actor)
      (haction member hmember)
    calc
      member * (implementer⁻¹ * actor) = implementer⁻¹ * (implementer * member * implementer⁻¹) * actor := by group
      _ = implementer⁻¹ * (actor * member * actor⁻¹) * actor := heq.symm
      _ = (implementer⁻¹ * actor) * member := by group
  rw [layer_centralizer_eq_bot hfree, Subgroup.mem_bot] at hcentralizer
  have heq : actor = implementer := (inv_mul_eq_one.mp hcentralizer).symm
  rwa [heq]

theorem involution_component_enters_layer {G : Type*} [Group G] [Finite G]
    (hfree : SolvableRadical.Free G) (element : G) (hsquare : element * element = 1)
    (houter : ∀ component : Subgroup G, IsComponentOf component ⊤ →
      Group.IsSolvable (OuterAutomorphisms.Outer (component ⧸ Subgroup.center component)))
    (localComponent : Subgroup (Subgroup.centralizer ({element} : Set G)))
    (hlocal : IsComponentOf localComponent ⊤) :
    localComponent.map (Subgroup.centralizer ({element} : Set G)).subtype ≤ Layer.subgroup G := by
  let centralizer := Subgroup.centralizer ({element} : Set G)
  let layer := Layer.subgroup G
  let : layer.Normal := Layer.normal G
  let localLayer := layer.subgroupOf centralizer
  let : localLayer.Normal := inferInstance
  rcases LocalComponents.normal_contains_or_commutes localComponent localLayer hlocal with
    hcontained | hcommutes
  · intro member hmember
    obtain ⟨lift, hlift, rfl⟩ := Subgroup.mem_map.mp hmember
    exact hcontained hlift
  · let image := localComponent.map centralizer.subtype
    let : Group.IsPerfect image := ⟨(Components.quasisimple_of_equiv
      (localComponent.equivMapOfInjective centralizer.subtype centralizer.subtype_injective).symm
      hlocal.2.2).1⟩
    have hfixed : ⁅image, layer ⊓ centralizer⁆ = ⊥ := by
      have hmap := congrArg (Subgroup.map centralizer.subtype) hcommutes
      change ⁅localComponent, layer.subgroupOf centralizer⁆.map centralizer.subtype =
        (⊥ : Subgroup centralizer).map centralizer.subtype at hmap
      simpa only [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
        Subgroup.map_bot] using hmap
    have hcenter : ⁅image, (Subgroup.center layer).map layer.subtype⁆ = ⊥ := by
      have hbot := center_eq_bot (SolvableRadical.free_normal_subgroup hfree layer)
      rw [hbot, Subgroup.map_bot, Subgroup.commutator_bot_right]
    apply perfect_normalizer_enters_layer hfree image _ houter
    intro component hcomponent
    exact ComponentAutomorphisms.ambient_normalizes_components image element hsquare
      (Subgroup.map_subtype_le _) hcenter hfixed component hcomponent

theorem component_center_eq_bot {G : Type*} [Group G] [Finite G]
    (hfree : SolvableRadical.Free G) (component : Subgroup G)
    (hcomponent : IsComponentOf component ⊤) : Subgroup.center component = ⊥ := by
  let layer := Layer.subgroup G
  let : layer.Normal := Layer.normal G
  have hlayerFree := SolvableRadical.free_normal_subgroup hfree layer
  let localComponent := component.subgroupOf layer
  let : localComponent.Normal := Layer.normal_component hcomponent
  let center := Subgroup.center localComponent
  let image := center.map localComponent.subtype
  let : image.Normal := ConjAct.normal_of_characteristic_of_normal
  let : Group.IsSolvable center := Group.isSolvable_of_comm
    (fun left right => (isMulCommutative_iff.mp inferInstance) left right)
  let : Group.IsSolvable image := Group.isSolvable_of_isSolvable_injective
    (f := (center.equivMapOfInjective localComponent.subtype localComponent.subtype_injective).symm.toMonoidHom)
    (center.equivMapOfInjective localComponent.subtype localComponent.subtype_injective).symm.injective
  have himage : image = ⊥ := hlayerFree image inferInstance inferInstance
  have hcenter : center = ⊥ := Subgroup.map_subtype_inj.mp
    (by simpa only [Subgroup.map_bot] using himage)
  let equivalence := Subgroup.subgroupOfEquivOfLe (Layer.component_le hcomponent)
  apply le_antisymm _ bot_le
  intro member hmember
  have hpreimage : equivalence.symm member ∈ center := by
    apply Subgroup.mem_center_iff.mpr
    intro other
    apply equivalence.injective
    simpa only [map_mul, equivalence.apply_symm_apply] using
      Subgroup.mem_center_iff.mp hmember (equivalence other)
  rw [hcenter, Subgroup.mem_bot] at hpreimage
  exact Subgroup.mem_bot.mpr (equivalence.symm.injective
    (hpreimage.trans equivalence.symm.map_one.symm))

theorem component_simple {G : Type*} [Group G] [Finite G]
    (hfree : SolvableRadical.Free G) (component : Subgroup G)
    (hcomponent : IsComponentOf component ⊤) : IsSimpleGroup component := by
  have hcenter := component_center_eq_bot hfree component hcomponent
  let projection := QuotientGroup.mk' (Subgroup.center component)
  have hkernel : projection.ker = ⊥ := by rw [QuotientGroup.ker_mk', hcenter]
  let equivalence := MulEquiv.ofBijective projection
    ⟨(MonoidHom.ker_eq_bot_iff projection).mp hkernel, QuotientGroup.mk'_surjective _⟩
  let : IsSimpleGroup (component ⧸ Subgroup.center component) := hcomponent.2.2.2
  exact equivalence.isSimpleGroup

end CFSG.ComponentClassification.RadicalFreeLayer
