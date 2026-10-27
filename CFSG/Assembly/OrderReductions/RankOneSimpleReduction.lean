module

public import CFSG.Assembly.OrderReductions.RankOneInduction

public section

namespace CFSG.OrderReductions.RankOneSimpleReduction

universe group_universe

open CFSG.OrderReductions.InvolutionGraph

theorem coreFree_centrality_of_simple_rank_one
    (simple_rank_one : ∀ (group : Type group_universe) [Group group] [Finite group]
      [IsSimpleGroup group], Even (Nat.card group) →
        CFSG.OrderReductions.RankOneInduction.NoFourInvolutions group → IsMulCommutative group)
    (group : Type group_universe) [Group group] [Finite group]
    (no_four : CFSG.OrderReductions.RankOneInduction.NoFourInvolutions group)
    (core_bot : CFSG.OrderReductions.OddCore.oddCore group = ⊥) (involution : Involution group) :
    involution.val ∈ Subgroup.center group := by
  classical
  generalize cardinality_eq : Nat.card group = cardinality
  induction cardinality using Nat.strong_induction_on generalizing group with
  | h cardinality induction_hypothesis =>
      have involution_ne_one : involution.val ≠ 1 := by
        intro equal_one
        have order_eq := involution.property
        rw [equal_one, orderOf_one] at order_eq
        omega
      have : Nontrivial group := nontrivial_of_ne involution.val 1 involution_ne_one
      by_cases proper_normal : ∃ normal : Subgroup group,
          normal.Normal ∧ normal ≠ ⊥ ∧ normal ≠ ⊤
      · obtain ⟨normal, normal_normal, normal_nontrivial, normal_proper⟩ := proper_normal
        have := normal_normal
        have even_normal : Even (Nat.card normal) := by
          by_contra not_even
          have normal_le := CFSG.OrderReductions.OddCore.normal_le_oddCore normal
            (Nat.not_even_iff_odd.mp not_even)
          rw [core_bot] at normal_le
          exact normal_nontrivial (le_bot_iff.mp normal_le)
        have : Fact (Nat.Prime 2) := ⟨by decide⟩
        obtain ⟨element, element_order⟩ := exists_prime_orderOf_dvd_card' 2
          (even_iff_two_dvd.mp even_normal)
        let internal : Involution normal := ⟨element, element_order⟩
        have smaller : Nat.card normal < cardinality := by
          rw [← cardinality_eq]
          exact CFSG.OrderReductions.Reduction.proper_subgroup_card_lt group normal normal_proper
        have internal_central := induction_hypothesis (Nat.card normal) smaller normal
          (CFSG.OrderReductions.RankOneInduction.noFourInvolutions_subgroup no_four normal)
          (CFSG.OrderReductions.OddCore.normal_subgroup_oddCore_eq_bot core_bot normal) internal rfl
        let ambient := mapInvolution normal.subtype Subtype.val_injective internal
        have ambient_central : ambient.val ∈ Subgroup.center group :=
          CFSG.OrderReductions.RankOneInduction.involution_central_of_normal_centrality no_four normal
            ambient element.property internal_central
        have equal_involutions := no_four involution ambient
          (Subgroup.mem_center_iff.mp ambient_central involution.val)
        exact equal_involutions.symm ▸ ambient_central
      · have : IsSimpleGroup group := by
          constructor
          intro normal normal_normal
          by_cases normal_bot : normal = ⊥
          · exact Or.inl normal_bot
          · exact Or.inr (by
              by_contra normal_proper
              exact proper_normal ⟨normal, normal_normal, normal_bot, normal_proper⟩)
        have even_group : Even (Nat.card group) := by
          apply even_iff_two_dvd.mpr
          have divides := orderOf_dvd_natCard involution.val
          rwa [involution.property] at divides
        have commutative := simple_rank_one group even_group no_four
        apply Subgroup.mem_center_iff.mpr
        intro element
        exact isMulCommutative_iff.mp commutative element involution.val

theorem coreFree_centrality_of_nonsolvable_simple_rank_one
    (simple_rank_one : ∀ (group : Type group_universe) [Group group] [Finite group]
      [IsSimpleGroup group], ¬ Group.IsSolvable group → Even (Nat.card group) →
        CFSG.OrderReductions.RankOneInduction.NoFourInvolutions group → False)
    (group : Type group_universe) [Group group] [Finite group]
    (no_four : CFSG.OrderReductions.RankOneInduction.NoFourInvolutions group)
    (core_bot : CFSG.OrderReductions.OddCore.oddCore group = ⊥) (involution : Involution group) :
    involution.val ∈ Subgroup.center group := by
  apply coreFree_centrality_of_simple_rank_one (group := group) (no_four := no_four)
    (core_bot := core_bot) (involution := involution)
  intro current current_group current_finite current_simple current_even current_no_four
  by_cases solvable : Group.IsSolvable current
  · have := solvable
    exact CFSG.OrderReductions.Helpers.simple_solvable_isMulCommutative current
  · exact False.elim (simple_rank_one current solvable current_even current_no_four)

end CFSG.OrderReductions.RankOneSimpleReduction
