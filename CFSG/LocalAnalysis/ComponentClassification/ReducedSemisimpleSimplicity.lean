module

public import CFSG.LocalAnalysis.ComponentClassification.SemisimpleComponentStructure
public import CFSG.LocalAnalysis.ComponentClassification.SemisimpleNormalGeneration

public section

open CFSG.Open

namespace CFSG.ComponentClassification.ReducedSemisimpleSimplicity

theorem layer_derived_simple_of_containment {G : Type*} [Group G] [Finite G]
    (hfree : SolvableRadical.Free G) (element : G) (horder : orderOf element = 2)
    (localComponent : Subgroup (Subgroup.centralizer ({element} : Set G)))
    (hlocal : TwoComponents.IsTwoComponent localComponent)
    (hnotQuasisimple : ¬ IsQuasisimple localComponent)
    (hcontained : localComponent.map (Subgroup.centralizer ({element} : Set G)).subtype ≤ Layer.subgroup G)
    (hcover : Subgroup.normalClosure
      (localComponent.map (Subgroup.centralizer ({element} : Set G)).subtype : Set G) ⊔
        Subgroup.zpowers element = ⊤) :
    Layer.subgroup G = commutator G ∧ IsSimpleGroup (commutator G) := by
  let image := localComponent.map (Subgroup.centralizer ({element} : Set G)).subtype
  let : Group.IsPerfect localComponent := ⟨TwoComponents.perfect hlocal⟩
  let : Group.IsPerfect image := Group.IsPerfect.map _
  have hequalities := SemisimpleNormalGeneration.layer_eq_normalClosure_eq_derived_of_containment
    element image hcontained hcover
  have hlayerDerived := hequalities.1.trans hequalities.2
  let : (Layer.subgroup G).Normal := Layer.normal G
  obtain ⟨fixedComponent, hfixed, hfixedNotQuasi, himage⟩ :=
    FixedNormalCentralizer.local_component_transport (Layer.subgroup G) element localComponent
      hlocal hnotQuasisimple hcontained
  have hclosure : Subgroup.normalClosure
      ((fixedComponent.map (FixedCommutingProduct.fixedSubgroup
        (MulAut.conjNormal (H := Layer.subgroup G) element)).subtype).map
          (Layer.subgroup G).subtype : Set G) = Layer.subgroup G := by
    rw [himage]
    exact hequalities.1.symm
  have hlayerCover : Layer.subgroup G ⊔ Subgroup.zpowers element = ⊤ := by
    rwa [hequalities.1]
  have hsquare : element * element = 1 := by
    have hpower := pow_orderOf_eq_one element
    rwa [horder, pow_two] at hpower
  let : IsSimpleGroup (Layer.subgroup G) :=
    SemisimpleComponentStructure.layer_simple_of_local_normalClosure hfree element hsquare
      fixedComponent hfixed hfixedNotQuasi hclosure hlayerCover
  exact ⟨hlayerDerived, (MulEquiv.subgroupCongr hlayerDerived).symm.isSimpleGroup⟩

theorem layer_derived_simple {G : Type*} [Group G] [Finite G]
    (hfree : SolvableRadical.Free G) (element : G) (horder : orderOf element = 2)
    (heven : ∀ component : Subgroup G, IsComponentOf component ⊤ → 2 ∣ Nat.card component)
    (houter : ∀ component : Subgroup G, IsComponentOf component ⊤ →
      Group.IsSolvable (OuterAutomorphisms.Outer (component ⧸ Subgroup.center component)))
    (localComponent : Subgroup (Subgroup.centralizer ({element} : Set G)))
    (hlocal : TwoComponents.IsTwoComponent localComponent)
    (hnotQuasisimple : ¬ IsQuasisimple localComponent)
    (hcover : Subgroup.normalClosure
      (localComponent.map (Subgroup.centralizer ({element} : Set G)).subtype : Set G) ⊔
        Subgroup.zpowers element = ⊤) :
    Layer.subgroup G = commutator G ∧ IsSimpleGroup (commutator G) := by
  exact layer_derived_simple_of_containment hfree element horder localComponent hlocal hnotQuasisimple
    (SemisimpleLocalContainment.component_enters_layer hfree element horder heven houter
      localComponent hlocal) hcover

theorem layer_derived_simple_of_proper_component_inputs {G : Type*} [Group G] [Finite G]
    (hfree : SolvableRadical.Free G) (element : G) (horder : orderOf element = 2)
    (heven : ∀ component : Subgroup G, IsComponentOf component ⊤ → component ≠ ⊤ → 2 ∣ Nat.card component)
    (houter : ∀ component : Subgroup G, IsComponentOf component ⊤ → component ≠ ⊤ →
      Group.IsSolvable (OuterAutomorphisms.Outer (component ⧸ Subgroup.center component)))
    (localComponent : Subgroup (Subgroup.centralizer ({element} : Set G)))
    (hlocal : TwoComponents.IsTwoComponent localComponent)
    (hnotQuasisimple : ¬ IsQuasisimple localComponent)
    (hcover : Subgroup.normalClosure
      (localComponent.map (Subgroup.centralizer ({element} : Set G)).subtype : Set G) ⊔
        Subgroup.zpowers element = ⊤) :
    Layer.subgroup G = commutator G ∧ IsSimpleGroup (commutator G) := by
  by_cases hlayerTop : Layer.subgroup G = ⊤
  · apply layer_derived_simple_of_containment hfree element horder localComponent hlocal hnotQuasisimple
    · rw [hlayerTop]
      exact le_top
    · exact hcover
  · have hproper : ∀ component : Subgroup G, IsComponentOf component ⊤ → component ≠ ⊤ := by
      intro component hcomponent htop
      apply hlayerTop
      apply top_unique
      rw [← htop]
      exact Layer.component_le hcomponent
    exact layer_derived_simple hfree element horder
      (fun component hcomponent => heven component hcomponent (hproper component hcomponent))
      (fun component hcomponent => houter component hcomponent (hproper component hcomponent))
        localComponent hlocal hnotQuasisimple hcover

end CFSG.ComponentClassification.ReducedSemisimpleSimplicity
