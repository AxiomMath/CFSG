module

public import CFSG.LocalAnalysis.ComponentClassification.InvolutionLayer
public import CFSG.LocalAnalysis.ComponentClassification.OddKernelInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayerTransport

public section

open CFSG.Open

namespace CFSG.ComponentClassification.OddQuotientLocalRecognition

theorem perfect_in_core_local_enters_twoLayer {G : Type*} [Group G] [Finite G]
    [Group.IsSolvable (componentClassificationOddCore G)]
    (element : G) (horder : orderOf element = 2)
    (perfectSubgroup : Subgroup G) [Group.IsPerfect perfectSubgroup]
    (hlocal : IsComponentOf
      ((perfectSubgroup.map (QuotientGroup.mk' (componentClassificationOddCore G))).subgroupOf
        (Subgroup.centralizer
          ({(QuotientGroup.mk' (componentClassificationOddCore G)) element} :
            Set (G ⧸ componentClassificationOddCore G)))) ⊤)
    (hcentralizes : perfectSubgroup ≤ Subgroup.centralizer ({element} : Set G))
    (houter : ∀ component : Subgroup (G ⧸ componentClassificationOddCore G),
      IsComponentOf component ⊤ →
        Group.IsSolvable (OuterAutomorphisms.Outer (component ⧸ Subgroup.center component))) :
    perfectSubgroup ≤ TwoLayer.subgroup G := by
  let projection := QuotientGroup.mk' (componentClassificationOddCore G)
  have hodd : Odd (Nat.card projection.ker) := by
    rw [QuotientGroup.ker_mk']
    exact OddCore.odd_card G
  have himageLe : perfectSubgroup.map projection ≤
      Subgroup.centralizer ({projection element} : Set (G ⧸ componentClassificationOddCore G)) := by
    rintro member ⟨lift, hlift, rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg projection (Subgroup.mem_centralizer_singleton_iff.mp (hcentralizes hlift))
  have hcontained := InvolutionLayer.component_enters_layer (OddCore.quotient_corefree G)
    (projection element) (OddKernelInvolutions.image_order projection hodd element horder) houter
    _ hlocal
  rw [Subgroup.map_subgroupOf_eq_of_le himageLe] at hcontained
  exact TwoLayerTransport.perfect_lift_from_core_quotient_layer perfectSubgroup hcontained

theorem local_twoComponent_quasisimple_of_core_image_of_twoLayer {G : Type*} [Group G] [Finite G]
    [Group.IsSolvable (componentClassificationOddCore G)]
    (element : G) (_horder : orderOf element = 2)
    (component : Subgroup G) (hcentralizes : component ≤ Subgroup.centralizer ({element} : Set G))
    (htwoComponent : TwoComponents.IsTwoComponent
      (component.subgroupOf (Subgroup.centralizer ({element} : Set G))))
    (hnotBad : ¬ component ≤ TwoComponents.badSubgroup G)
    (hlocal : IsComponentOf
      ((component.map (QuotientGroup.mk' (componentClassificationOddCore G))).subgroupOf
        (Subgroup.centralizer
          ({(QuotientGroup.mk' (componentClassificationOddCore G)) element} :
            Set (G ⧸ componentClassificationOddCore G)))) ⊤)
    (htwoLayer : component ≤ TwoLayer.subgroup G) :
    component ≤ Layer.subgroup G ∧ IsQuasisimple component := by
  let : Group.IsPerfect (component.subgroupOf (Subgroup.centralizer ({element} : Set G))) :=
    ⟨TwoComponents.perfect htwoComponent⟩
  let : Group.IsPerfect component := Group.IsPerfect.ofSurjective
    (f := (Subgroup.subgroupOfEquivOfLe hcentralizes).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hcentralizes).surjective
  have hdichotomy := TwoLayer.local_component_in_layer_or_bad element
    (component.subgroupOf (Subgroup.centralizer ({element} : Set G))) htwoComponent
    (by rw [Subgroup.map_subgroupOf_eq_of_le hcentralizes]; exact htwoLayer)
  rw [Subgroup.map_subgroupOf_eq_of_le hcentralizes] at hdichotomy
  have hleLayer := hdichotomy.resolve_right hnotBad
  have hcentralizesCore : component ≤ Subgroup.centralizer
      (componentClassificationOddCore G : Set G) := by
    let : (componentClassificationOddCore G).Normal := inferInstance
    have hcommutes := Layer.commutes_with_solvable_subnormal (componentClassificationOddCore G)
      (Components.chain_of_mathlib_subnormal
        (inferInstance : (componentClassificationOddCore G).Normal).isSubnormal)
    exact hleLayer.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes)
  let projection := QuotientGroup.mk' (componentClassificationOddCore G)
  let image := component.map projection
  let restriction : component →* image :=
    (projection.domRestrict component).codRestrict image
      (fun member => Subgroup.mem_map_of_mem projection member.property)
  have hsurjective : Function.Surjective restriction := by
    intro member
    obtain ⟨lift, hlift, heq⟩ := Subgroup.mem_map.mp member.property
    exact ⟨⟨lift, hlift⟩, Subtype.ext heq⟩
  have hkernel : restriction.ker ≤ Subgroup.center component := by
    intro member hmember
    have hcore : member.val ∈ componentClassificationOddCore G := (QuotientGroup.eq_one_iff _).mp
      (congrArg Subtype.val (MonoidHom.mem_ker.mp hmember))
    apply Subgroup.mem_center_iff.mpr
    intro other
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp
      (hcentralizesCore other.property) member.val hcore).symm
  have himageLe : image ≤ Subgroup.centralizer
      ({projection element} : Set (G ⧸ componentClassificationOddCore G)) := by
    rintro member ⟨lift, hlift, rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg projection (Subgroup.mem_centralizer_singleton_iff.mp (hcentralizes hlift))
  have hquasisimple : IsQuasisimple image := Components.quasisimple_of_equiv
    (Subgroup.subgroupOfEquivOfLe himageLe).symm hlocal.2.2
  exact ⟨hleLayer, CentralExtensions.quasisimple_of_surjective hquasisimple restriction
    hsurjective hkernel⟩

theorem local_twoComponent_quasisimple_of_core_image {G : Type*} [Group G] [Finite G]
    [Group.IsSolvable (componentClassificationOddCore G)]
    (element : G) (horder : orderOf element = 2)
    (component : Subgroup G) (hcentralizes : component ≤ Subgroup.centralizer ({element} : Set G))
    (htwoComponent : TwoComponents.IsTwoComponent
      (component.subgroupOf (Subgroup.centralizer ({element} : Set G))))
    (hnotBad : ¬ component ≤ TwoComponents.badSubgroup G)
    (hlocal : IsComponentOf
      ((component.map (QuotientGroup.mk' (componentClassificationOddCore G))).subgroupOf
        (Subgroup.centralizer
          ({(QuotientGroup.mk' (componentClassificationOddCore G)) element} :
            Set (G ⧸ componentClassificationOddCore G)))) ⊤)
    (houter : ∀ ambientComponent : Subgroup (G ⧸ componentClassificationOddCore G),
      IsComponentOf ambientComponent ⊤ →
        Group.IsSolvable (OuterAutomorphisms.Outer
          (ambientComponent ⧸ Subgroup.center ambientComponent))) :
    component ≤ Layer.subgroup G ∧ IsQuasisimple component := by
  let : Group.IsPerfect (component.subgroupOf (Subgroup.centralizer ({element} : Set G))) :=
    ⟨TwoComponents.perfect htwoComponent⟩
  let : Group.IsPerfect component := Group.IsPerfect.ofSurjective
    (f := (Subgroup.subgroupOfEquivOfLe hcentralizes).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hcentralizes).surjective
  exact local_twoComponent_quasisimple_of_core_image_of_twoLayer element horder component hcentralizes
    htwoComponent hnotBad hlocal
      (perfect_in_core_local_enters_twoLayer element horder component hlocal hcentralizes houter)

theorem perfect_in_core_local_enters_twoLayer_of_proper_outer {G : Type*} [Group G] [Finite G]
    [Group.IsSolvable (componentClassificationOddCore G)]
    (element : G) (horder : orderOf element = 2)
    (perfectSubgroup : Subgroup G) [Group.IsPerfect perfectSubgroup]
    (hlocal : IsComponentOf
      ((perfectSubgroup.map (QuotientGroup.mk' (componentClassificationOddCore G))).subgroupOf
        (Subgroup.centralizer
          ({(QuotientGroup.mk' (componentClassificationOddCore G)) element} :
            Set (G ⧸ componentClassificationOddCore G)))) ⊤)
    (hcentralizes : perfectSubgroup ≤ Subgroup.centralizer ({element} : Set G))
    (houter : ∀ component : Subgroup (G ⧸ componentClassificationOddCore G),
      IsComponentOf component ⊤ → component ≠ ⊤ →
        Group.IsSolvable (OuterAutomorphisms.Outer (component ⧸ Subgroup.center component))) :
    perfectSubgroup ≤ TwoLayer.subgroup G := by
  by_cases hlayerTop : Layer.subgroup (G ⧸ componentClassificationOddCore G) = ⊤
  · apply TwoLayerTransport.perfect_lift_from_core_quotient_layer perfectSubgroup
    rw [hlayerTop]
    exact le_top
  · apply perfect_in_core_local_enters_twoLayer element horder perfectSubgroup hlocal hcentralizes
    intro component hcomponent
    apply houter component hcomponent
    intro htop
    apply hlayerTop
    apply top_unique
    rw [← htop]
    exact Layer.component_le hcomponent

theorem local_twoComponent_quasisimple_of_core_image_of_proper_outer
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable (componentClassificationOddCore G)]
    (element : G) (horder : orderOf element = 2)
    (component : Subgroup G) (hcentralizes : component ≤ Subgroup.centralizer ({element} : Set G))
    (htwoComponent : TwoComponents.IsTwoComponent
      (component.subgroupOf (Subgroup.centralizer ({element} : Set G))))
    (hnotBad : ¬ component ≤ TwoComponents.badSubgroup G)
    (hlocal : IsComponentOf
      ((component.map (QuotientGroup.mk' (componentClassificationOddCore G))).subgroupOf
        (Subgroup.centralizer
          ({(QuotientGroup.mk' (componentClassificationOddCore G)) element} :
            Set (G ⧸ componentClassificationOddCore G)))) ⊤)
    (houter : ∀ ambientComponent : Subgroup (G ⧸ componentClassificationOddCore G),
      IsComponentOf ambientComponent ⊤ → ambientComponent ≠ ⊤ →
        Group.IsSolvable (OuterAutomorphisms.Outer
          (ambientComponent ⧸ Subgroup.center ambientComponent))) :
    component ≤ Layer.subgroup G ∧ IsQuasisimple component := by
  let : Group.IsPerfect (component.subgroupOf (Subgroup.centralizer ({element} : Set G))) :=
    ⟨TwoComponents.perfect htwoComponent⟩
  let : Group.IsPerfect component := Group.IsPerfect.ofSurjective
    (f := (Subgroup.subgroupOfEquivOfLe hcentralizes).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hcentralizes).surjective
  exact local_twoComponent_quasisimple_of_core_image_of_twoLayer element horder component hcentralizes
    htwoComponent hnotBad hlocal (perfect_in_core_local_enters_twoLayer_of_proper_outer
      element horder component hlocal hcentralizes houter)

theorem core_local_image_of_odd_quotient {G : Type*} [Group G] [Finite G]
    [Group.IsSolvable (componentClassificationOddCore G)]
    (oddNormal : Subgroup G) [oddNormal.Normal] (hodd : Odd (Nat.card oddNormal))
    (element : G) (horder : orderOf element = 2) (subgroup : Subgroup G)
    (hcentralizes : subgroup ≤ Subgroup.centralizer ({element} : Set G))
    (hlocal : IsComponentOf
      ((subgroup.map (QuotientGroup.mk' oddNormal)).subgroupOf
        (Subgroup.centralizer ({(QuotientGroup.mk' oddNormal) element} : Set (G ⧸ oddNormal)))) ⊤) :
    IsComponentOf
      ((subgroup.map (QuotientGroup.mk' (componentClassificationOddCore G))).subgroupOf
        (Subgroup.centralizer
          ({(QuotientGroup.mk' (componentClassificationOddCore G)) element} :
            Set (G ⧸ componentClassificationOddCore G)))) ⊤ := by
  let projection := QuotientGroup.mk' oddNormal
  let coreProjection := QuotientGroup.mk' (componentClassificationOddCore G)
  have hle : oddNormal ≤ coreProjection.ker := by
    rw [QuotientGroup.ker_mk']
    exact OddCore.maximal G oddNormal inferInstance hodd
  let factor := QuotientGroup.lift oddNormal coreProjection hle
  have hcomposite : factor.comp projection = coreProjection :=
    QuotientGroup.lift_comp_mk' oddNormal coreProjection hle
  have hfactorSurjective : Function.Surjective factor := by
    intro member
    obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (componentClassificationOddCore G) member
    exact ⟨projection lift, congrArg (fun homomorphism : G →* (G ⧸ componentClassificationOddCore G) =>
      homomorphism lift) hcomposite⟩
  let kernelCover : componentClassificationOddCore G →* factor.ker :=
    (projection.domRestrict (componentClassificationOddCore G)).codRestrict factor.ker
      (by
        intro member
        apply MonoidHom.mem_ker.mpr
        have heq := congrArg (fun homomorphism : G →* (G ⧸ componentClassificationOddCore G) =>
          homomorphism member.val) hcomposite
        exact heq.trans ((QuotientGroup.eq_one_iff _).mpr member.property))
  have hcoverSurjective : Function.Surjective kernelCover := by
    intro member
    obtain ⟨lift, hlift⟩ := QuotientGroup.mk'_surjective oddNormal member.val
    have hcore : lift ∈ componentClassificationOddCore G := by
      apply (QuotientGroup.eq_one_iff _).mp
      change coreProjection lift = 1
      have heq := congrArg (fun homomorphism : G →* (G ⧸ componentClassificationOddCore G) =>
        homomorphism lift) hcomposite
      change factor (projection lift) = coreProjection lift at heq
      change projection lift = member.val at hlift
      rw [← heq, hlift]
      exact MonoidHom.mem_ker.mp member.property
    exact ⟨⟨lift, hcore⟩, Subtype.ext hlift⟩
  let : Group.IsSolvable factor.ker := Group.isSolvable_of_surjective hcoverSurjective
  have hfactorOdd : Odd (Nat.card factor.ker) :=
    (OddCore.odd_card G).of_dvd_nat (CFSG.card_dvd_of_surjective kernelCover hcoverSurjective)
  have hprojectionOdd : Odd (Nat.card projection.ker) := by
    rw [QuotientGroup.ker_mk']
    exact hodd
  have himageLe : subgroup.map projection ≤
      Subgroup.centralizer ({projection element} : Set (G ⧸ oddNormal)) := by
    rintro member ⟨lift, hlift, rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg projection (Subgroup.mem_centralizer_singleton_iff.mp (hcentralizes hlift))
  have htransport := OddKernelInvolutions.component_image factor hfactorSurjective hfactorOdd
    (projection element) (OddKernelInvolutions.image_order projection hprojectionOdd element horder)
    _ hlocal
  rw [Subgroup.map_subgroupOf_eq_of_le himageLe, Subgroup.map_map, hcomposite] at htransport
  have helement : factor (projection element) = coreProjection element :=
    congrArg (fun homomorphism : G →* (G ⧸ componentClassificationOddCore G) =>
      homomorphism element) hcomposite
  rw [helement] at htransport
  exact htransport

theorem perfect_in_odd_local_enters_twoLayer {G : Type*} [Group G] [Finite G]
    [Group.IsSolvable (componentClassificationOddCore G)]
    (oddNormal : Subgroup G) [oddNormal.Normal] (hodd : Odd (Nat.card oddNormal))
    (element : G) (horder : orderOf element = 2)
    (perfectSubgroup : Subgroup G) [Group.IsPerfect perfectSubgroup]
    (hcentralizes : perfectSubgroup ≤ Subgroup.centralizer ({element} : Set G))
    (hlocal : IsComponentOf
      ((perfectSubgroup.map (QuotientGroup.mk' oddNormal)).subgroupOf
        (Subgroup.centralizer ({(QuotientGroup.mk' oddNormal) element} : Set (G ⧸ oddNormal)))) ⊤)
    (houter : ∀ component : Subgroup (G ⧸ componentClassificationOddCore G),
      IsComponentOf component ⊤ →
        Group.IsSolvable (OuterAutomorphisms.Outer (component ⧸ Subgroup.center component))) :
    perfectSubgroup ≤ TwoLayer.subgroup G :=
  perfect_in_core_local_enters_twoLayer element horder perfectSubgroup
    (core_local_image_of_odd_quotient oddNormal hodd element horder perfectSubgroup hcentralizes hlocal)
    hcentralizes houter

theorem local_twoComponent_quasisimple_of_odd_image {G : Type*} [Group G] [Finite G]
    [Group.IsSolvable (componentClassificationOddCore G)]
    (oddNormal : Subgroup G) [oddNormal.Normal] (hodd : Odd (Nat.card oddNormal))
    (element : G) (horder : orderOf element = 2)
    (component : Subgroup G) (hcentralizes : component ≤ Subgroup.centralizer ({element} : Set G))
    (htwoComponent : TwoComponents.IsTwoComponent
      (component.subgroupOf (Subgroup.centralizer ({element} : Set G))))
    (hnotBad : ¬ component ≤ TwoComponents.badSubgroup G)
    (hlocal : IsComponentOf
      ((component.map (QuotientGroup.mk' oddNormal)).subgroupOf
        (Subgroup.centralizer ({(QuotientGroup.mk' oddNormal) element} : Set (G ⧸ oddNormal)))) ⊤)
    (houter : ∀ ambientComponent : Subgroup (G ⧸ componentClassificationOddCore G),
      IsComponentOf ambientComponent ⊤ →
        Group.IsSolvable (OuterAutomorphisms.Outer
          (ambientComponent ⧸ Subgroup.center ambientComponent))) :
    component ≤ Layer.subgroup G ∧ IsQuasisimple component :=
  local_twoComponent_quasisimple_of_core_image element horder component hcentralizes htwoComponent
    hnotBad (core_local_image_of_odd_quotient oddNormal hodd element horder component hcentralizes hlocal)
    houter

theorem local_twoComponent_quasisimple_of_odd_image_of_proper_outer
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable (componentClassificationOddCore G)]
    (oddNormal : Subgroup G) [oddNormal.Normal] (hodd : Odd (Nat.card oddNormal))
    (element : G) (horder : orderOf element = 2)
    (component : Subgroup G) (hcentralizes : component ≤ Subgroup.centralizer ({element} : Set G))
    (htwoComponent : TwoComponents.IsTwoComponent
      (component.subgroupOf (Subgroup.centralizer ({element} : Set G))))
    (hnotBad : ¬ component ≤ TwoComponents.badSubgroup G)
    (hlocal : IsComponentOf
      ((component.map (QuotientGroup.mk' oddNormal)).subgroupOf
        (Subgroup.centralizer ({(QuotientGroup.mk' oddNormal) element} : Set (G ⧸ oddNormal)))) ⊤)
    (houter : ∀ ambientComponent : Subgroup (G ⧸ componentClassificationOddCore G),
      IsComponentOf ambientComponent ⊤ → ambientComponent ≠ ⊤ →
        Group.IsSolvable (OuterAutomorphisms.Outer
          (ambientComponent ⧸ Subgroup.center ambientComponent))) :
    component ≤ Layer.subgroup G ∧ IsQuasisimple component :=
  local_twoComponent_quasisimple_of_core_image_of_proper_outer element horder component hcentralizes
    htwoComponent hnotBad
      (core_local_image_of_odd_quotient oddNormal hodd element horder component hcentralizes hlocal) houter

end CFSG.ComponentClassification.OddQuotientLocalRecognition
