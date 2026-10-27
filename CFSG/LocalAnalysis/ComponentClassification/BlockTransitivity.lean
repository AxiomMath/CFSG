module

public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationAction

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockTransitivity

theorem exists_actor {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (factor : Subgroup G) (hfactor : factor ∈ UniversalOrbitBlock.block component) :
    ∃ actor ∈ UniversalOrbitBlock.normalizer component, UniversalOrbitBlock.conjugate component actor = factor := by
  obtain ⟨actor, heq⟩ := hfactor.1
  refine ⟨actor, ?_, heq.symm⟩
  exact UniversalOrbitBlock.normalizes_of_anchor_image component heven huniversal hquasisimple component
    (UniversalOrbitBlock.mem_block_self component) actor (heq ▸ hfactor)

theorem exists_between {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (first second : Subgroup G) (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component) :
    ∃ actor ∈ UniversalOrbitBlock.normalizer component, UniversalOrbitBlock.conjugate first actor = second := by
  obtain ⟨firstActor, hfirstActor, hfirstImage⟩ := exists_actor component heven huniversal hquasisimple first hfirst
  obtain ⟨secondActor, hsecondActor, hsecondImage⟩ := exists_actor component heven huniversal hquasisimple second hsecond
  refine ⟨secondActor * firstActor⁻¹, (UniversalOrbitBlock.normalizer component).mul_mem hsecondActor
    ((UniversalOrbitBlock.normalizer component).inv_mem hfirstActor), ?_⟩
  rw [← hfirstImage, UniversalOrbitBlock.conjugate_conjugate, mul_assoc, inv_mul_cancel, mul_one]
  exact hsecondImage

theorem pretransitive {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component) :
    let := BlockPermutationAction.action component heven huniversal hquasisimple
    MulAction.IsPretransitive (UniversalOrbitBlock.normalizer component) ↥(UniversalOrbitBlock.block component) := by
  let := BlockPermutationAction.action component heven huniversal hquasisimple
  refine ⟨?_⟩
  intro first second
  obtain ⟨actor, hactor, heq⟩ := exists_between component heven huniversal hquasisimple first.val second.val
    first.property second.property
  exact ⟨⟨actor, hactor⟩, Subtype.ext heq⟩

theorem stabilizer {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (factor : ↥(UniversalOrbitBlock.block component)) :
    let := BlockPermutationAction.action component heven huniversal hquasisimple
    MulAction.stabilizer (UniversalOrbitBlock.normalizer component) factor =
      (Subgroup.normalizer (factor.val : Set G)).subgroupOf (UniversalOrbitBlock.normalizer component) := by
  let := BlockPermutationAction.action component heven huniversal hquasisimple
  ext actor
  rw [MulAction.mem_stabilizer_iff]
  change (⟨UniversalOrbitBlock.conjugate factor.val actor.val, _⟩ : ↥(UniversalOrbitBlock.block component)) = factor ↔
    actor.val ∈ Subgroup.normalizer (factor.val : Set G)
  exact Subtype.ext_iff.trans (CommutingComponentFamily.normalizer_iff_conjugate_eq factor.val actor.val).symm

theorem index {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (factor : Subgroup G) (hfactor : factor ∈ UniversalOrbitBlock.block component) :
    ((Subgroup.normalizer (factor : Set G)).subgroupOf (UniversalOrbitBlock.normalizer component)).index =
      Nat.card ↥(UniversalOrbitBlock.block component) := by
  let blockAction := BlockPermutationAction.action component heven huniversal hquasisimple
  let actionTransitive : @MulAction.IsPretransitive (UniversalOrbitBlock.normalizer component)
      ↥(UniversalOrbitBlock.block component) blockAction.toSMul :=
    pretransitive component heven huniversal hquasisimple
  have hindex := @MulAction.index_stabilizer_of_transitive (UniversalOrbitBlock.normalizer component)
    ↥(UniversalOrbitBlock.block component) inferInstance blockAction ⟨factor, hfactor⟩ actionTransitive
  exact (congrArg Subgroup.index (stabilizer component heven huniversal hquasisimple ⟨factor, hfactor⟩)).symm.trans hindex

theorem card {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (factor : Subgroup G) (hfactor : factor ∈ UniversalOrbitBlock.block component) :
    Nat.card (UniversalOrbitBlock.normalizer component) = Nat.card (Subgroup.normalizer (factor : Set G)) *
      Nat.card ↥(UniversalOrbitBlock.block component) := by
  have hle := UniversalOrbitBlock.factor_normalizer_le component heven huniversal hquasisimple factor hfactor
  have hcard := ((Subgroup.normalizer (factor : Set G)).subgroupOf (UniversalOrbitBlock.normalizer component)).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    index component heven huniversal hquasisimple factor hfactor] at hcard
  exact hcard.symm

end CFSG.ComponentClassification.BlockTransitivity
