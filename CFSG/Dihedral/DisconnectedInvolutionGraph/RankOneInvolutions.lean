module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.InvolutionGraph

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G] [Finite G]

@[expose] def NoCommutingDistinctInvolutions (G : Type*) [Group G] : Prop :=
  ∀ first second : Involution G,
    (first : G) * second = (second : G) * first → first = second

theorem rank_one_two_group_unique_involution [Nontrivial G]
    (hpgroup : IsPGroup 2 G) (hrank : NoCommutingDistinctInvolutions G) :
    ∃ central : Involution G, (central : G) ∈ Subgroup.center G ∧
      ∀ involution : Involution G, involution = central := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Nontrivial (Subgroup.center G) := hpgroup.center_nontrivial
  have hdiv : 2 ∣ Nat.card (Subgroup.center G) := by
    rcases (hpgroup.to_subgroup (Subgroup.center G)).card_eq_or_dvd with hone | hdiv
    · have hsubsingleton : Subsingleton (Subgroup.center G) :=
        (Nat.card_eq_one_iff_unique.mp hone).1
      exact (not_subsingleton (Subgroup.center G) hsubsingleton).elim
    · exact hdiv
  obtain ⟨element, horder⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center G) 2 hdiv
  let central : Involution G := ⟨element, (Subgroup.orderOf_coe element).trans horder⟩
  refine ⟨central, element.property, ?_⟩
  intro involution
  exact hrank involution central (Subgroup.mem_center_iff.mp element.property involution)

theorem rank_one_two_group_unique_order_two_subgroup [Nontrivial G]
    (hpgroup : IsPGroup 2 G) (hrank : NoCommutingDistinctInvolutions G) :
    ∃ subgroup : Subgroup G, Nat.card subgroup = 2 ∧
      ∀ other : Subgroup G, Nat.card other = 2 → other = subgroup := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨central, _, hunique⟩ := rank_one_two_group_unique_involution hpgroup hrank
  let subgroup := Subgroup.zpowers (central : G)
  have hcard : Nat.card subgroup = 2 := (Nat.card_zpowers (central : G)).trans central.property
  refine ⟨subgroup, hcard, ?_⟩
  intro other hotherCard
  obtain ⟨element, horder⟩ := exists_prime_orderOf_dvd_card' (G := other) 2
    (by rw [hotherCard])
  let involution : Involution G := ⟨element, (Subgroup.orderOf_coe element).trans horder⟩
  have heq : (central : G) = element := congrArg Subtype.val (hunique involution).symm
  have hle : subgroup ≤ other := by
    apply Subgroup.zpowers_le.mpr
    rw [heq]
    exact element.property
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hotherCard])).symm

omit [Finite G] in
theorem subgroup_no_commuting_distinct_involutions (subgroup : Subgroup G)
    (hrank : NoCommutingDistinctInvolutions G) : NoCommutingDistinctInvolutions subgroup := by
  intro first second hcommute
  let firstAmbient : Involution G := ⟨first.val, (Subgroup.orderOf_coe first.val).trans first.property⟩
  let secondAmbient : Involution G := ⟨second.val,
    (Subgroup.orderOf_coe second.val).trans second.property⟩
  have heq := hrank firstAmbient secondAmbient
    (congrArg (fun element : subgroup => (element : G)) hcommute)
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun involution : Involution G => involution.val) heq

end CFSG.DisconnectedInvolutionGraph.Helpers
