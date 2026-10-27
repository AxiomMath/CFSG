module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

open CFSG.Open

namespace CFSG.ComponentClassification.ComponentInnerActions

theorem perfect_normalizer_action_inner {G : Type*} [Group G]
    (perfectSubgroup component : Subgroup G) [Group.IsPerfect perfectSubgroup]
    (hnormalizes : perfectSubgroup ≤ Subgroup.normalizer (component : Set G))
    [Group.IsSolvable (OuterAutomorphisms.Outer component)] (actor : perfectSubgroup) :
    ∃ implementer ∈ component, ∀ member ∈ component,
      actor.val * member * actor.val⁻¹ = implementer * member * implementer⁻¹ := by
  let action : perfectSubgroup →* MulAut component :=
    component.normalizerMonoidHom.comp (Subgroup.inclusion hnormalizes)
  obtain ⟨implementer, heq⟩ := OuterAutomorphisms.perfect_action_inner action actor
  refine ⟨implementer.val, implementer.property, ?_⟩
  intro member hmember
  exact congrArg (fun automorphism : MulAut component =>
    (automorphism (⟨member, hmember⟩ : component)).val) heq

theorem exists_layer_implementer {G : Type*} [Group G] [Finite G] (actor : G)
    (hinner : ∀ component : Subgroup G, IsComponentOf component ⊤ →
      ∃ implementer ∈ component, ∀ member ∈ component,
        actor * member * actor⁻¹ = implementer * member * implementer⁻¹) :
    ∃ implementer ∈ Layer.subgroup G, ∀ member ∈ Layer.subgroup G,
      actor * member * actor⁻¹ = implementer * member * implementer⁻¹ := by
  classical
  have hpatch : ∀ components : Finset (Subgroup G),
      (∀ component ∈ components, IsComponentOf component ⊤) →
      ∃ implementer ∈ sSup (components : Set (Subgroup G)),
        ∀ component ∈ components, ∀ member ∈ component,
          actor * member * actor⁻¹ = implementer * member * implementer⁻¹ := by
    intro components
    induction components using Finset.induction_on with
    | empty =>
        intro _
        exact ⟨1, Subgroup.one_mem _, by simp⟩
    | @insert component components hnotMem hinduction =>
        intro hall
        have hcomponent := hall component (Finset.mem_insert_self _ _)
        obtain ⟨implementer, himplementer, himplements⟩ := hinner component hcomponent
        obtain ⟨tail, htail, htailAction⟩ := hinduction
          (fun other hother => hall other (Finset.mem_insert_of_mem hother))
        have htailCentralizes : sSup (components : Set (Subgroup G)) ≤
            Subgroup.centralizer (component : Set G) := by
          apply sSup_le
          intro other hother
          have hotherNe : other ≠ component := by
            intro heq
            subst other
            exact hnotMem hother
          exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
            (LocalComponents.commute_of_ne other component
              (hall other (Finset.mem_insert_of_mem hother)) hcomponent hotherNe)
        refine ⟨implementer * tail, ?_, ?_⟩
        · rw [Finset.coe_insert, sSup_insert]
          exact Subgroup.mul_mem_sup himplementer htail
        · intro other hother member hmember
          rcases Finset.mem_insert.mp hother with heq | hotherTail
          · subst other
            have hcommute := Subgroup.mem_centralizer_iff.mp
              (htailCentralizes htail) member hmember
            calc
              actor * member * actor⁻¹ = implementer * member * implementer⁻¹ :=
                himplements member hmember
              _ = (implementer * tail) * member * (implementer * tail)⁻¹ := by
                rw [mul_inv_rev]
                calc
                  implementer * member * implementer⁻¹ =
                      implementer * (member * tail) * tail⁻¹ * implementer⁻¹ := by group
                  _ = implementer * (tail * member) * tail⁻¹ * implementer⁻¹ := by rw [hcommute]
                  _ = implementer * tail * member * (tail⁻¹ * implementer⁻¹) := by group
          · have hotherComponent := hall other (Finset.mem_insert_of_mem hotherTail)
            have hotherNe : component ≠ other := by
              intro heq
              subst other
              exact hnotMem hotherTail
            have hcentralizes := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
              (LocalComponents.commute_of_ne component other hcomponent hotherComponent hotherNe)
            calc
              actor * member * actor⁻¹ = tail * member * tail⁻¹ :=
                htailAction other hotherTail member hmember
              _ = implementer * (tail * member * tail⁻¹) * implementer⁻¹ := by
                have htailValue : tail * member * tail⁻¹ ∈ other := by
                  let : (other.subgroupOf (Layer.subgroup G)).Normal :=
                    Layer.normal_component hotherComponent
                  have htailLayer : tail ∈ Layer.subgroup G := by
                    apply (show sSup (components : Set (Subgroup G)) ≤ Layer.subgroup G from ?_) htail
                    apply sSup_le
                    intro candidate hcandidate
                    exact Layer.component_le (hall candidate (Finset.mem_insert_of_mem hcandidate))
                  exact (inferInstance : (other.subgroupOf (Layer.subgroup G)).Normal).conj_mem
                    (⟨member, Layer.component_le hotherComponent hmember⟩ : Layer.subgroup G) hmember
                    (⟨tail, htailLayer⟩ : Layer.subgroup G)
                have hconjugateCommute := Subgroup.mem_centralizer_iff.mp
                  (hcentralizes himplementer) _ htailValue
                rw [← hconjugateCommute]
                group
              _ = (implementer * tail) * member * (implementer * tail)⁻¹ := by group
  let componentSet : Set (Subgroup G) := {component | IsComponentOf component ⊤}
  have hfinite := Set.toFinite componentSet
  obtain ⟨implementer, himplementer, himplements⟩ := hpatch hfinite.toFinset
    (by
      intro component hcomponent
      change component ∈ componentSet
      exact hfinite.mem_toFinset.mp hcomponent)
  have hset : (hfinite.toFinset : Set (Subgroup G)) = componentSet := hfinite.coe_toFinset
  rw [hset] at himplementer
  refine ⟨implementer, himplementer, ?_⟩
  have hbound : Layer.subgroup G ≤
      (MulAut.conj actor).toMonoidHom.eqLocus (MulAut.conj implementer).toMonoidHom := by
    apply sSup_le
    intro component hcomponent member hmember
    exact himplements component (hfinite.mem_toFinset.mpr hcomponent) member hmember
  intro member hmember
  exact hbound hmember

end CFSG.ComponentClassification.ComponentInnerActions
