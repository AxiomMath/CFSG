module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.CommutingActorFixedSubgroups

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G A : Type*} [Group G] [CommGroup A] [MulDistribMulAction A G]

theorem nilpotent_odd_commuting_involutions_fixed_generate [Finite G] [Group.IsNilpotent G]
    (hodd : Odd (Nat.card G)) (first second : A)
    (hfirstSquare : first * first = 1) (hsecondSquare : second * second = 1) :
    (actorFixedSubgroup (G := G) first ⊔ actorFixedSubgroup (G := G) second) ⊔
      actorFixedSubgroup (G := G) (first * second) = ⊤ := by
  let generated := (actorFixedSubgroup (G := G) first ⊔ actorFixedSubgroup (G := G) second) ⊔
    actorFixedSubgroup (G := G) (first * second)
  have hinvariant : InvariantSubgroup (A := A) generated :=
    invariant_subgroup_sup _ _
      (invariant_subgroup_sup _ _ (commuting_actor_fixed_subgroup_invariant first)
        (commuting_actor_fixed_subgroup_invariant second))
      (commuting_actor_fixed_subgroup_invariant (first * second))
  let normalizer := Subgroup.normalizer (generated : Set G)
  let _ := invariantSubgroupAction normalizer (invariant_subgroup_normalizer generated hinvariant)
  let within := generated.subgroupOf normalizer
  have hwithinInvariant : InvariantSubgroup (A := A) within := by
    intro actor element hmem
    exact hinvariant actor element.val hmem
  have hwithinOdd : Odd (Nat.card within) :=
    (hodd.of_dvd_nat normalizer.card_subgroup_dvd_card).of_dvd_nat within.card_subgroup_dvd_card
  have hwithinTop : within = ⊤ := by
    apply commuting_involutions_fixed_subgroups_generate_of_normal first second hfirstSquare
      hsecondSquare within hwithinInvariant hwithinOdd
    · intro element hfixed
      have hfixedAmbient : first • element.val = element.val := congrArg Subtype.val hfixed
      change element.val ∈ generated
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hfixedAmbient)
    · intro element hfixed
      have hfixedAmbient : second • element.val = element.val := congrArg Subtype.val hfixed
      change element.val ∈ generated
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hfixedAmbient)
    · intro element hfixed
      have hfixedAmbient : (first * second) • element.val = element.val :=
        congrArg Subtype.val hfixed
      change element.val ∈ generated
      exact Subgroup.mem_sup_right hfixedAmbient
  have hselfNormalizer : normalizer = generated := by
    apply le_antisymm _ Subgroup.le_normalizer
    intro element hmem
    have hwithin : (⟨element, hmem⟩ : normalizer) ∈ within := by
      rw [hwithinTop]
      trivial
    exact hwithin
  exact normalizerCondition_iff_only_full_group_self_normalizing.mp
    Group.normalizerCondition_of_isNilpotent generated hselfNormalizer

end CFSG.DisconnectedInvolutionGraph.Helpers
