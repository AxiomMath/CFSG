module

public import CFSG.LocalAnalysis.ComponentClassification.InvolutionLayerOrbitLocation
public import CFSG.LocalAnalysis.ComponentClassification.UniversalComponentBlock
public import CFSG.LocalAnalysis.ComponentClassification.OddQuotientLocalRecognition

public section

open CFSG.Open

namespace CFSG.ComponentClassification.OrdinaryLocalPumpUp

theorem twoLayer_le_layer {G : Type*} [Group G]
    (hordinary : ∀ component : Subgroup G, TwoComponents.IsTwoComponent component →
      IsComponentOf component ⊤) : TwoLayer.subgroup G ≤ Layer.subgroup G := by
  apply sSup_le
  intro component hcomponent
  exact Layer.component_le (hordinary component hcomponent)

theorem ordinary_local_enters_twoLayer {G : Type*} [Group G] [Finite G]
    [Group.IsSolvable (componentClassificationOddCore G)]
    (element : G) (horder : orderOf element = 2) (component : Subgroup G)
    (hcentralizer : component ≤ Subgroup.centralizer {element})
    (hcomponent : IsComponentOf (component.subgroupOf (Subgroup.centralizer {element})) ⊤)
    (houter : ∀ factor : Subgroup (G ⧸ componentClassificationOddCore G), IsComponentOf factor ⊤ →
      Group.IsSolvable (OuterAutomorphisms.Outer (factor ⧸ Subgroup.center factor))) :
    component ≤ TwoLayer.subgroup G := by
  let equivalence : G ≃* G ⧸ (⊥ : Subgroup G) := QuotientGroup.quotientBot.symm
  have hprojection : equivalence.toMonoidHom = QuotientGroup.mk' (⊥ : Subgroup G) := by
    ext member
    rfl
  have hlocal := OrdinaryComponentTransport.map_nested equivalence component
    (Subgroup.centralizer {element}) hcomponent
  rw [UniversalComponentBlock.singleton_centralizer_map, hprojection] at hlocal
  let : Group.IsPerfect (component.subgroupOf (Subgroup.centralizer {element})) := ⟨hcomponent.2.2.1⟩
  let inclusion := Subgroup.subgroupOfEquivOfLe hcentralizer
  let : Group.IsPerfect component :=
    Group.IsPerfect.ofSurjective (f := inclusion.toMonoidHom) inclusion.surjective
  exact OddQuotientLocalRecognition.perfect_in_odd_local_enters_twoLayer
    (⊥ : Subgroup G) (by rw [Subgroup.card_bot]; decide) element horder component hcentralizer hlocal houter

theorem enters_layer {G : Type*} [Group G] [Finite G]
    [Group.IsSolvable (componentClassificationOddCore G)]
    (hordinary : ∀ component : Subgroup G, TwoComponents.IsTwoComponent component →
      IsComponentOf component ⊤)
    (element : G) (horder : orderOf element = 2) (component : Subgroup G)
    (hcentralizer : component ≤ Subgroup.centralizer {element})
    (hcomponent : IsComponentOf (component.subgroupOf (Subgroup.centralizer {element})) ⊤)
    (houter : ∀ factor : Subgroup (G ⧸ componentClassificationOddCore G), IsComponentOf factor ⊤ →
      Group.IsSolvable (OuterAutomorphisms.Outer (factor ⧸ Subgroup.center factor))) :
    component ≤ Layer.subgroup G :=
  (ordinary_local_enters_twoLayer element horder component hcentralizer hcomponent houter).trans
    (twoLayer_le_layer hordinary)

theorem pump_up {G : Type*} [Group G] [Finite G]
    [Group.IsSolvable (componentClassificationOddCore G)]
    (hordinary : ∀ component : Subgroup G, TwoComponents.IsTwoComponent component →
      IsComponentOf component ⊤)
    (element : G) (horder : orderOf element = 2) (component : Subgroup G)
    (hcentralizer : component ≤ Subgroup.centralizer {element})
    (hcomponent : IsComponentOf (component.subgroupOf (Subgroup.centralizer {element})) ⊤)
    (houter : ∀ factor : Subgroup (G ⧸ componentClassificationOddCore G), IsComponentOf factor ⊤ →
      Group.IsSolvable (OuterAutomorphisms.Outer (factor ⧸ Subgroup.center factor))) :
    component ≤ Layer.subgroup G ∧
      ∃ factor : Subgroup G, IsComponentOf factor ⊤ ∧
        ((factor.map (MulAut.conj element).toMonoidHom = factor ∧ component ≤ factor ∧
          IsComponentOf (component.subgroupOf (factor ⊓ Subgroup.centralizer {element})) ⊤) ∨
        (∃ hcommutes : ⁅factor, factor.map (MulAut.conj element).toMonoidHom⁆ = ⊥,
          factor.map (MulAut.conj element).toMonoidHom ≠ factor ∧
          component = (InvolutionDiagonal.homomorphism factor (MulAut.conj element) hcommutes).range)) := by
  have hcontained := enters_layer hordinary element horder component hcentralizer hcomponent houter
  have hsquare : element * element = 1 := by
    rw [← pow_two, ← horder]
    exact pow_orderOf_eq_one element
  exact ⟨hcontained, InvolutionLayerOrbitLocation.location element hsquare
    component hcentralizer hcomponent hcontained⟩

theorem enters_twoLayer_of_proper_outer {G : Type*} [Group G] [Finite G]
    [Group.IsSolvable (componentClassificationOddCore G)]
    (element : G) (horder : orderOf element = 2) (component : Subgroup G)
    (hcentralizer : component ≤ Subgroup.centralizer {element})
    (hcomponent : IsComponentOf (component.subgroupOf (Subgroup.centralizer {element})) ⊤)
    (houter : ∀ factor : Subgroup (G ⧸ componentClassificationOddCore G), IsComponentOf factor ⊤ → factor ≠ ⊤ →
      Group.IsSolvable (OuterAutomorphisms.Outer (factor ⧸ Subgroup.center factor))) :
    component ≤ TwoLayer.subgroup G := by
  let equivalence : G ≃* G ⧸ (⊥ : Subgroup G) := QuotientGroup.quotientBot.symm
  have hprojection : equivalence.toMonoidHom = QuotientGroup.mk' (⊥ : Subgroup G) := by ext member; rfl
  have hlocal := OrdinaryComponentTransport.map_nested equivalence component
    (Subgroup.centralizer {element}) hcomponent
  rw [UniversalComponentBlock.singleton_centralizer_map, hprojection] at hlocal
  have hcoreLocal := OddQuotientLocalRecognition.core_local_image_of_odd_quotient
    (⊥ : Subgroup G) (by rw [Subgroup.card_bot]; decide) element horder component hcentralizer hlocal
  let : Group.IsPerfect (component.subgroupOf (Subgroup.centralizer {element})) := ⟨hcomponent.2.2.1⟩
  let inclusion := Subgroup.subgroupOfEquivOfLe hcentralizer
  let : Group.IsPerfect component :=
    Group.IsPerfect.ofSurjective (f := inclusion.toMonoidHom) inclusion.surjective
  exact OddQuotientLocalRecognition.perfect_in_core_local_enters_twoLayer_of_proper_outer
    element horder component hcoreLocal hcentralizer houter

theorem enters_layer_of_proper_outer {G : Type*} [Group G] [Finite G]
    [Group.IsSolvable (componentClassificationOddCore G)]
    (hordinary : ∀ component : Subgroup G, TwoComponents.IsTwoComponent component →
      IsComponentOf component ⊤)
    (element : G) (horder : orderOf element = 2) (component : Subgroup G)
    (hcentralizer : component ≤ Subgroup.centralizer {element})
    (hcomponent : IsComponentOf (component.subgroupOf (Subgroup.centralizer {element})) ⊤)
    (houter : ∀ factor : Subgroup (G ⧸ componentClassificationOddCore G), IsComponentOf factor ⊤ → factor ≠ ⊤ →
      Group.IsSolvable (OuterAutomorphisms.Outer (factor ⧸ Subgroup.center factor))) :
    component ≤ Layer.subgroup G :=
  (enters_twoLayer_of_proper_outer element horder component hcentralizer hcomponent houter).trans
    (twoLayer_le_layer hordinary)

end CFSG.ComponentClassification.OrdinaryLocalPumpUp
