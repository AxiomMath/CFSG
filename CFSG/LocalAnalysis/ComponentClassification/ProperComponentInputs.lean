module

public import CFSG.LocalAnalysis.ComponentClassification.ReducedSemisimpleSimplicity

public section

open CFSG.Open

namespace CFSG.ComponentClassification.ProperComponentInputs

theorem component_order {G : Type*} [Group G] [Finite G]
    (hK : IsKProperByOrder G) (hfree : SolvableRadical.Free G) (component : Subgroup G)
    (hcomponent : IsComponentOf component ⊤) (hproper : component ≠ ⊤) :
    Nat.card component ∈ knownSimpleOrders := by
  let : IsSimpleGroup component := RadicalFreeLayer.component_simple hfree component hcomponent
  let : Group.IsPerfect component := ⟨hcomponent.2.2.1⟩
  have hnonab : ∃ left right : component, left * right ≠ right * left := by
    have hnoncomm := Group.IsPerfect.not_isMulCommutative component
    simpa only [isMulCommutative_iff, not_forall] using hnoncomm
  exact Helpers.simple_quotient_order_of_surjective G hK component hproper component hnonab
    (MonoidHom.id component) Function.surjective_id

theorem even_of_odd_order_solvable {G : Type*} [Group G] [Finite G]
    (hodd : ∀ (subgroup : Subgroup G), Odd (Nat.card subgroup) → Group.IsSolvable subgroup)
    (component : Subgroup G) (hcomponent : IsComponentOf component ⊤) :
    2 ∣ Nat.card component := by
  by_contra hnotEven
  have hoddCard : Odd (Nat.card component) := Nat.not_even_iff_odd.mp
    (fun heven => hnotEven (even_iff_two_dvd.mp heven))
  let : Group.IsPerfect component := ⟨hcomponent.2.2.1⟩
  let : Nontrivial component := Quasisimple.nontrivial hcomponent.2.2
  exact Group.IsPerfect.not_isSolvable component (hodd component hoddCard)

theorem layer_derived_simple {G : Type*} [Group G] [Finite G]
    (hK : IsKProperByOrder G) (hfree : SolvableRadical.Free G)
    (hodd : ∀ (subgroup : Subgroup G), Odd (Nat.card subgroup) → Group.IsSolvable subgroup)
    (hschreier : ∀ (component : Subgroup G), IsSimpleGroup component →
      (∃ left right : component, left * right ≠ right * left) →
        Nat.card component ∈ knownSimpleOrders →
          Group.IsSolvable (OuterAutomorphisms.Outer component))
    (element : G) (horder : orderOf element = 2)
    (localComponent : Subgroup (Subgroup.centralizer ({element} : Set G)))
    (hlocal : TwoComponents.IsTwoComponent localComponent)
    (hnotQuasisimple : ¬ IsQuasisimple localComponent)
    (hcover : Subgroup.normalClosure
      (localComponent.map (Subgroup.centralizer ({element} : Set G)).subtype : Set G) ⊔
        Subgroup.zpowers element = ⊤) :
    Layer.subgroup G = commutator G ∧ IsSimpleGroup (commutator G) := by
  apply ReducedSemisimpleSimplicity.layer_derived_simple_of_proper_component_inputs
    hfree element horder _ _ localComponent hlocal hnotQuasisimple hcover
  · intro component hcomponent _
    exact even_of_odd_order_solvable hodd component hcomponent
  · intro component hcomponent hproper
    have hsimple := RadicalFreeLayer.component_simple hfree component hcomponent
    let : IsSimpleGroup component := hsimple
    let : Group.IsPerfect component := ⟨hcomponent.2.2.1⟩
    have hnonab : ∃ left right : component, left * right ≠ right * left := by
      have hnoncomm := Group.IsPerfect.not_isMulCommutative component
      simpa only [isMulCommutative_iff, not_forall] using hnoncomm
    let : Group.IsSolvable (OuterAutomorphisms.Outer component) :=
      hschreier component hsimple hnonab (component_order hK hfree component hcomponent hproper)
    have hcenter := RadicalFreeLayer.component_center_eq_bot hfree component hcomponent
    let projection := QuotientGroup.mk' (Subgroup.center component)
    have hkernel : projection.ker = ⊥ := by rw [QuotientGroup.ker_mk', hcenter]
    let groupEquivalence := MulEquiv.ofBijective projection
      ⟨(MonoidHom.ker_eq_bot_iff projection).mp hkernel, QuotientGroup.mk'_surjective _⟩
    exact OuterAutomorphisms.solvable_of_equiv groupEquivalence

end CFSG.ComponentClassification.ProperComponentInputs
