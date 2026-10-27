module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.NilpotentOddFixedGeneration

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G A : Type*} [Group G] [CommGroup A] [MulDistribMulAction A G]

theorem odd_two_group_action_commuting_involutions_fixed_generate [Finite G]
    (hpgroup : IsPGroup 2 A) (hodd : Odd (Nat.card G)) (first second : A)
    (hfirstSquare : first * first = 1) (hsecondSquare : second * second = 1) :
    (actorFixedSubgroup (G := G) first ⊔ actorFixedSubgroup (G := G) second) ⊔
      actorFixedSubgroup (G := G) (first * second) = ⊤ := by
  classical
  let generated := (actorFixedSubgroup (G := G) first ⊔ actorFixedSubgroup (G := G) second) ⊔
    actorFixedSubgroup (G := G) (first * second)
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hindexNe : generated.index ≠ 1 := fun heq => hne (Subgroup.index_eq_one.mp heq)
  obtain ⟨prime, hprime, hprimeDiv⟩ := Nat.exists_prime_and_dvd hindexNe
  let _ : Fact (Nat.Prime prime) := ⟨hprime⟩
  have hcoprime : ¬ 2 ∣ Nat.card G :=
    fun hdiv => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdiv)
  obtain ⟨sylow, hinvariant⟩ := coprime_pgroup_exists_invariant_sylow 2 prime hpgroup hcoprime
  let _ := invariantSubgroupAction (sylow : Subgroup G) hinvariant
  have _ : Group.IsNilpotent (sylow : Subgroup G) := sylow.isPGroup'.isNilpotent
  have hsylowOdd : Odd (Nat.card (sylow : Subgroup G)) :=
    hodd.of_dvd_nat (sylow : Subgroup G).card_subgroup_dvd_card
  have hgenerated := nilpotent_odd_commuting_involutions_fixed_generate hsylowOdd
    first second hfirstSquare hsecondSquare
  let within := generated.subgroupOf (sylow : Subgroup G)
  have hfirstFixed : actorFixedSubgroup (G := (sylow : Subgroup G)) first ≤ within := by
    intro element hfixed
    change element.val ∈ generated
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left
      (congrArg (fun element : (sylow : Subgroup G) => element.val) hfixed))
  have hsecondFixed : actorFixedSubgroup (G := (sylow : Subgroup G)) second ≤ within := by
    intro element hfixed
    change element.val ∈ generated
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right
      (congrArg (fun element : (sylow : Subgroup G) => element.val) hfixed))
  have hproductFixed : actorFixedSubgroup (G := (sylow : Subgroup G)) (first * second) ≤ within := by
    intro element hfixed
    change element.val ∈ generated
    exact Subgroup.mem_sup_right
      (congrArg (fun element : (sylow : Subgroup G) => element.val) hfixed)
  have hwithinTop : within = ⊤ := top_le_iff.mp (by
    rw [← hgenerated]
    exact sup_le (sup_le hfirstFixed hsecondFixed) hproductFixed)
  have hsylowLe : (sylow : Subgroup G) ≤ generated := by
    intro element hmem
    have hwithin : (⟨element, hmem⟩ : (sylow : Subgroup G)) ∈ within := by
      rw [hwithinTop]
      trivial
    exact hwithin
  exact sylow.not_dvd_index (hprimeDiv.trans (Subgroup.index_dvd_of_le hsylowLe))

end CFSG.DisconnectedInvolutionGraph.Helpers
