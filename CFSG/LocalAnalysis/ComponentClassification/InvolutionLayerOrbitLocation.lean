module

public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionOrbitComponentLocation
public import CFSG.LocalAnalysis.ComponentClassification.SemisimpleComponentStructure

public section

open CFSG.Open

namespace CFSG.ComponentClassification.InvolutionLayerOrbitLocation

theorem location {G : Type*} [Group G] [Finite G] (element : G)
    (hsquare : element * element = 1) (component : Subgroup G)
    (hcentralizer : component ≤ Subgroup.centralizer {element})
    (hcomponent : IsComponentOf (component.subgroupOf (Subgroup.centralizer {element})) ⊤)
    (hcontained : component ≤ Layer.subgroup G) :
    ∃ factor : Subgroup G, IsComponentOf factor ⊤ ∧
      ((factor.map (MulAut.conj element).toMonoidHom = factor ∧
        component ≤ factor ∧
        IsComponentOf (component.subgroupOf (factor ⊓ Subgroup.centralizer {element})) ⊤) ∨
      (∃ hcommutes : ⁅factor, factor.map (MulAut.conj element).toMonoidHom⁆ = ⊥,
        factor.map (MulAut.conj element).toMonoidHom ≠ factor ∧
        component = (InvolutionDiagonal.homomorphism factor (MulAut.conj element) hcommutes).range)) := by
  classical
  let layer := Layer.subgroup G
  let : layer.Normal := Layer.normal G
  let localAutomorphism := MulAut.conjNormal (H := layer) element
  let fixed := FixedCommutingProduct.fixedSubgroup localAutomorphism
  let centralizer := Subgroup.centralizer {element}
  let localLayer := layer.subgroupOf centralizer
  have hlocalLe : component.subgroupOf centralizer ≤ localLayer := by
    intro member hmember
    exact hcontained hmember
  let restricted := (component.subgroupOf centralizer).subgroupOf localLayer
  let equivalence := FixedNormalCentralizer.equivalence layer element
  let fixedComponent := restricted.map equivalence.toMonoidHom
  have hrestricted := LocalComponents.of_overgroup hcomponent hlocalLe
  have hfixedComponent : IsComponentOf fixedComponent ⊤ :=
    (LocalComponents.equiv_iff equivalence restricted).mpr hrestricted
  have hnormal : ∀ index : SemisimpleComponentStructure.ComponentIndex G,
      (SemisimpleComponentStructure.factor index).Normal :=
    fun index => Layer.normal_component index.property
  have hcommutes : Pairwise (fun first second : SemisimpleComponentStructure.ComponentIndex G =>
      ⁅SemisimpleComponentStructure.factor first, SemisimpleComponentStructure.factor second⁆ = ⊥) := by
    intro first second hne
    apply (Subgroup.map_eq_bot_iff_of_injective _ layer.subtype_injective).mp
    rw [Subgroup.map_commutator]
    change ⁅(first.val.subgroupOf layer).map layer.subtype,
      (second.val.subgroupOf layer).map layer.subtype⁆ = ⊥
    rw [Subgroup.map_subgroupOf_eq_of_le (Layer.component_le first.property),
      Subgroup.map_subgroupOf_eq_of_le (Layer.component_le second.property)]
    exact LocalComponents.commute_of_ne _ _ first.property second.property
      (fun heq => hne (Subtype.ext heq))
  have hquasisimple : ∀ index : SemisimpleComponentStructure.ComponentIndex G,
      IsQuasisimple (SemisimpleComponentStructure.factor index) :=
    fun index => (SemisimpleComponentStructure.factor_component index).2.2
  have hconjInvolutive : Function.Involutive (MulAut.conj element) := by
    intro member
    have hconjSquare : MulAut.conj element * MulAut.conj element = 1 := by
      rw [← map_mul, hsquare, map_one]
    exact congrArg (fun automorphism : MulAut G => automorphism member) hconjSquare
  have hlocalInvolutive : Function.Involutive localAutomorphism := by
    intro member
    exact Subtype.ext (hconjInvolutive member.val)
  have hcover : (⨆ index : SemisimpleComponentStructure.ComponentIndex G,
      SemisimpleComponentStructure.factor index) = ⊤ :=
    SemisimpleComponentStructure.factor_cover G
  obtain ⟨index, hcase⟩ := InvolutionOrbitComponentLocation.invariant_or_diagonal
    SemisimpleComponentStructure.factor hnormal hquasisimple hcommutes
    (SemisimpleComponentStructure.imageIndex (MulAut.conj element))
    (SemisimpleComponentStructure.imageIndex_involutive (MulAut.conj element) hconjInvolutive)
    localAutomorphism hlocalInvolutive (SemisimpleComponentStructure.factor_images element)
    fixedComponent hfixedComponent (by rw [hcover]; exact le_top)
  have hfactorMap : (SemisimpleComponentStructure.factor index).map layer.subtype = index.val :=
    Subgroup.map_subgroupOf_eq_of_le (Layer.component_le index.property)
  have hequivariance : layer.subtype.comp localAutomorphism.toMonoidHom =
      (MulAut.conj element).toMonoidHom.comp layer.subtype := by
    ext member
    exact MulAut.conjNormal_apply element member
  have hfixedImage : (fixedComponent.map fixed.subtype).map layer.subtype = component := by
    ext member
    constructor
    · rintro ⟨lift, ⟨original, ⟨preimage, hpreimage, rfl⟩, rfl⟩, rfl⟩
      exact hpreimage
    · intro hmember
      let original : restricted := ⟨⟨⟨member, hcentralizer hmember⟩, hcontained hmember⟩, hmember⟩
      exact ⟨_, ⟨_, Subgroup.mem_map_of_mem equivalence.toMonoidHom original.property, rfl⟩, rfl⟩
  refine ⟨index.val, index.property, ?_⟩
  rcases hcase with ⟨hinvariant, hle, _⟩ | ⟨hlocalCommutes, hlocalDifferent, hdiagonal⟩
  · have hinvariantAmbient := congrArg (Subgroup.map layer.subtype) hinvariant
    rw [Subgroup.map_map, hequivariance, ← Subgroup.map_map, hfactorMap] at hinvariantAmbient
    have hleAmbient := Subgroup.map_mono (f := layer.subtype) hle
    rw [hfixedImage, hfactorMap] at hleAmbient
    exact Or.inl ⟨hinvariantAmbient, hleAmbient,
      OrdinaryComponentTransport.restrict_nested component (index.val ⊓ centralizer) centralizer
        (le_inf hleAmbient hcentralizer) inf_le_right hcomponent⟩
  · have hcommutesAmbient : ⁅index.val, index.val.map (MulAut.conj element).toMonoidHom⁆ = ⊥ := by
      have hmap := congrArg (Subgroup.map layer.subtype) hlocalCommutes
      rw [Subgroup.map_commutator, Subgroup.map_map, hequivariance, ← Subgroup.map_map,
        hfactorMap, Subgroup.map_bot] at hmap
      exact hmap
    have hdifferentAmbient : index.val.map (MulAut.conj element).toMonoidHom ≠ index.val := by
      intro heq
      apply hlocalDifferent
      apply Subgroup.map_injective layer.subtype_injective
      rw [Subgroup.map_map, hequivariance, ← Subgroup.map_map, hfactorMap, heq]
    refine Or.inr ⟨hcommutesAmbient, hdifferentAmbient, ?_⟩
    have hmap := congrArg (Subgroup.map layer.subtype) hdiagonal
    rw [hfixedImage] at hmap
    have hdiagonalMap : (InvolutionDiagonal.homomorphism (SemisimpleComponentStructure.factor index)
        localAutomorphism hlocalCommutes).range.map layer.subtype =
        (InvolutionDiagonal.homomorphism index.val (MulAut.conj element) hcommutesAmbient).range := by
      ext member
      constructor
      · rintro ⟨lift, ⟨original, rfl⟩, rfl⟩
        exact ⟨⟨original.val.val, original.property⟩, rfl⟩
      · rintro ⟨original, rfl⟩
        exact ⟨_, ⟨⟨⟨original.val, Layer.component_le index.property original.property⟩,
          original.property⟩, rfl⟩, rfl⟩
    exact hmap.trans hdiagonalMap

end CFSG.ComponentClassification.InvolutionLayerOrbitLocation
