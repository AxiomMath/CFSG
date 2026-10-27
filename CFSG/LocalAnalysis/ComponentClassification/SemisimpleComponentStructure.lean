module

public import CFSG.LocalAnalysis.ComponentClassification.RadicalFreeLayer
public import CFSG.LocalAnalysis.ComponentClassification.SemisimpleFixedLocalComponents

public section

open CFSG.Open

namespace CFSG.ComponentClassification.SemisimpleComponentStructure

local instance layerNormal (G : Type*) [Group G] : (Layer.subgroup G).Normal := Layer.normal G

@[expose] def ComponentIndex (G : Type*) [Group G] := {component : Subgroup G // IsComponentOf component ⊤}

@[expose] noncomputable def factor {G : Type*} [Group G] (index : ComponentIndex G) : Subgroup (Layer.subgroup G) :=
  index.val.subgroupOf (Layer.subgroup G)

theorem factor_component {G : Type*} [Group G] (index : ComponentIndex G) :
    IsComponentOf (factor index) ⊤ :=
  LocalComponents.of_overgroup index.property (Layer.component_le index.property)

theorem factor_cover (G : Type*) [Group G] : (⨆ index : ComponentIndex G, factor index) = ⊤ := by
  have hmap : ∀ index : ComponentIndex G,
      (factor index).map (Layer.subgroup G).subtype = index.val := fun index =>
    Subgroup.map_subgroupOf_eq_of_le (Layer.component_le index.property)
  have hbound : Layer.subgroup G ≤ (⨆ index : ComponentIndex G, factor index).map
      (Layer.subgroup G).subtype := by
    apply sSup_le
    intro component hcomponent
    rw [Subgroup.map_iSup]
    change (⟨component, hcomponent⟩ : ComponentIndex G).val ≤ _
    rw [← hmap (⟨component, hcomponent⟩ : ComponentIndex G)]
    exact le_iSup (fun index : ComponentIndex G =>
      (factor index).map (Layer.subgroup G).subtype) (⟨component, hcomponent⟩ : ComponentIndex G)
  apply top_unique
  intro member _
  obtain ⟨lift, hlift, heq⟩ := Subgroup.mem_map.mp (hbound member.property)
  have heqSubtype : lift = member := Subtype.ext heq
  rwa [heqSubtype] at hlift

def imageIndex {G : Type*} [Group G] (automorphism : MulAut G) (index : ComponentIndex G) :
    ComponentIndex G :=
  ⟨index.val.map automorphism.toMonoidHom,
    (LocalComponents.equiv_iff automorphism index.val).mpr index.property⟩

theorem imageIndex_involutive {G : Type*} [Group G] (automorphism : MulAut G)
    (hinvolutive : Function.Involutive automorphism) : Function.Involutive (imageIndex automorphism) := by
  intro index
  apply Subtype.ext
  change (index.val.map automorphism.toMonoidHom).map automorphism.toMonoidHom = index.val
  rw [Subgroup.map_map]
  have hidentity : automorphism.toMonoidHom.comp automorphism.toMonoidHom = MonoidHom.id G := by
    ext member
    exact hinvolutive member
  rw [hidentity, Subgroup.map_id]

theorem factor_images {G : Type*} [Group G] (element : G) (index : ComponentIndex G) :
    (factor index).map (MulAut.conjNormal (H := Layer.subgroup G) element).toMonoidHom =
      factor (imageIndex (MulAut.conj element) index) := by
  let : (Layer.subgroup G).Normal := Layer.normal G
  apply Subgroup.map_injective (Layer.subgroup G).subtype_injective
  have hmaps : ∀ component : ComponentIndex G,
      (factor component).map (Layer.subgroup G).subtype = component.val := fun component =>
    Subgroup.map_subgroupOf_eq_of_le (Layer.component_le component.property)
  rw [hmaps, Subgroup.map_map]
  have hequivariance : (Layer.subgroup G).subtype.comp
      (MulAut.conjNormal (H := Layer.subgroup G) element).toMonoidHom =
        (MulAut.conj element).toMonoidHom.comp (Layer.subgroup G).subtype := by
    ext member
    exact MulAut.conjNormal_apply element member
  rw [hequivariance, ← Subgroup.map_map, hmaps]
  rfl

theorem layer_simple_of_local_normalClosure {G : Type*} [Group G] [Finite G]
    (hfree : SolvableRadical.Free G) (element : G) (hsquare : element * element = 1)
    (localComponent : Subgroup (FixedCommutingProduct.fixedSubgroup
      (MulAut.conjNormal (H := Layer.subgroup G) element)))
    (hlocal : TwoComponents.IsTwoComponent localComponent)
    (hnotQuasisimple : ¬ IsQuasisimple localComponent)
    (hclosure : Subgroup.normalClosure
      ((localComponent.map (FixedCommutingProduct.fixedSubgroup
        (MulAut.conjNormal (H := Layer.subgroup G) element)).subtype).map
          (Layer.subgroup G).subtype : Set G) = Layer.subgroup G)
    (hcover : Layer.subgroup G ⊔ Subgroup.zpowers element = ⊤) :
    IsSimpleGroup (Layer.subgroup G) := by
  classical
  let : (Layer.subgroup G).Normal := Layer.normal G
  let : Finite (ComponentIndex G) := by unfold ComponentIndex; infer_instance
  let : Fintype (ComponentIndex G) := Fintype.ofFinite _
  have hlayerFree := SolvableRadical.free_normal_subgroup hfree (Layer.subgroup G)
  have hnormal : ∀ index : ComponentIndex G, (factor index).Normal :=
    fun index => Layer.normal_component index.property
  have hcenter : ∀ index : ComponentIndex G, Subgroup.center (factor index) = ⊥ :=
    fun index => RadicalFreeLayer.component_center_eq_bot hlayerFree _ (factor_component index)
  have hsimple : ∀ index : ComponentIndex G, IsSimpleGroup (factor index) :=
    fun index => RadicalFreeLayer.component_simple hlayerFree _ (factor_component index)
  have hperfect : ∀ index : ComponentIndex G, Group.IsPerfect (factor index) :=
    fun index => ⟨(factor_component index).2.2.1⟩
  have hcommutes : Pairwise (fun first second : ComponentIndex G => ⁅factor first, factor second⁆ = ⊥) := by
    intro first second hne
    apply LocalComponents.commute_of_ne _ _ (factor_component first) (factor_component second)
    intro heq
    apply hne
    apply Subtype.ext
    have hmap := congrArg (Subgroup.map (Layer.subgroup G).subtype) heq
    simpa only [factor, Subgroup.map_subgroupOf_eq_of_le (Layer.component_le first.property),
      Subgroup.map_subgroupOf_eq_of_le (Layer.component_le second.property)] using hmap
  have hinvolutive : Function.Involutive (MulAut.conjNormal (H := Layer.subgroup G) element) := by
    intro member
    have heq : MulAut.conjNormal (H := Layer.subgroup G) element *
        MulAut.conjNormal (H := Layer.subgroup G) element = 1 := by
      rw [← map_mul, hsquare, map_one]
    exact congrArg (fun value : MulAut (Layer.subgroup G) => value member) heq
  have hambientInvolutive : Function.Involutive (MulAut.conj element) := by
    intro member
    have heq : MulAut.conj element * MulAut.conj element = 1 := by rw [← map_mul, hsquare, map_one]
    exact congrArg (fun value : MulAut G => value member) heq
  exact SemisimpleFixedLocalComponents.normalClosure_simple_extension (Layer.subgroup G) element
    factor hnormal hcenter hsimple hperfect hcommutes (factor_cover G)
      (imageIndex (MulAut.conj element)) (imageIndex_involutive _ hambientInvolutive)
        hinvolutive (factor_images element) localComponent hlocal hnotQuasisimple hclosure hcover

end CFSG.ComponentClassification.SemisimpleComponentStructure
