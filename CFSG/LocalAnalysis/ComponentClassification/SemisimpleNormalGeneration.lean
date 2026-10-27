module

public import CFSG.LocalAnalysis.ComponentClassification.LocalBNormalGeneration
public import CFSG.LocalAnalysis.ComponentClassification.SemisimpleLocalContainment

public section

open CFSG.Open

namespace CFSG.ComponentClassification.SemisimpleNormalGeneration

theorem layer_eq_normalClosure_eq_derived_of_containment {G : Type*} [Group G]
    (element : G) (perfectSubgroup : Subgroup G) [Group.IsPerfect perfectSubgroup]
    (hcontained : perfectSubgroup ≤ Layer.subgroup G)
    (hcover : Subgroup.normalClosure (perfectSubgroup : Set G) ⊔ Subgroup.zpowers element = ⊤) :
    Layer.subgroup G = Subgroup.normalClosure (perfectSubgroup : Set G) ∧
      Subgroup.normalClosure (perfectSubgroup : Set G) = commutator G := by
  let normalClosure := Subgroup.normalClosure (perfectSubgroup : Set G)
  let : (Layer.subgroup G).Normal := Layer.normal G
  let : Group.IsPerfect normalClosure := LocalBNormalGeneration.perfect_normalClosure perfectSubgroup
  have hclosureLayer : normalClosure ≤ Layer.subgroup G := Subgroup.normalClosure_le_normal hcontained
  have hclosureDerived : normalClosure = commutator G := by
    apply le_antisymm
    · calc
        normalClosure = ⁅normalClosure, normalClosure⁆ := Subgroup.commutator_eq_self.symm
        _ ≤ ⁅(⊤ : Subgroup G), ⊤⁆ := Subgroup.commutator_mono le_top le_top
        _ = commutator G := rfl
    · exact Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hcover inferInstance
  exact ⟨le_antisymm ((Layer.le_derived G).trans hclosureDerived.ge) hclosureLayer,
    hclosureDerived⟩

theorem layer_eq_normalClosure_eq_derived {G : Type*} [Group G] [Finite G]
    (hfree : SolvableRadical.Free G) (element : G) (horder : orderOf element = 2)
    (heven : ∀ component : Subgroup G, IsComponentOf component ⊤ → 2 ∣ Nat.card component)
    (houter : ∀ component : Subgroup G, IsComponentOf component ⊤ →
      Group.IsSolvable (OuterAutomorphisms.Outer (component ⧸ Subgroup.center component)))
    (localComponent : Subgroup (Subgroup.centralizer ({element} : Set G)))
    (hlocal : TwoComponents.IsTwoComponent localComponent)
    (hcover : Subgroup.normalClosure
      (localComponent.map (Subgroup.centralizer ({element} : Set G)).subtype : Set G) ⊔
        Subgroup.zpowers element = ⊤) :
    Layer.subgroup G = Subgroup.normalClosure
      (localComponent.map (Subgroup.centralizer ({element} : Set G)).subtype : Set G) ∧
    Subgroup.normalClosure
      (localComponent.map (Subgroup.centralizer ({element} : Set G)).subtype : Set G) =
        commutator G := by
  let image := localComponent.map (Subgroup.centralizer ({element} : Set G)).subtype
  let : Group.IsPerfect localComponent := ⟨TwoComponents.perfect hlocal⟩
  let : Group.IsPerfect image := Group.IsPerfect.map _
  exact layer_eq_normalClosure_eq_derived_of_containment element image
    (SemisimpleLocalContainment.component_enters_layer hfree element horder heven houter
      localComponent hlocal) hcover

end CFSG.ComponentClassification.SemisimpleNormalGeneration
