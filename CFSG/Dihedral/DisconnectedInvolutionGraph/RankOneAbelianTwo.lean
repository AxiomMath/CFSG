module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneInvolutions

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

theorem rank_one_abelian_two_group_cyclic (G : Type*) [CommGroup G] [Finite G]
    (hpgroup : IsPGroup 2 G) (hrank : NoCommutingDistinctInvolutions G) : IsCyclic G := by
  classical
  induction hcard : Nat.card G using Nat.strong_induction_on generalizing G with
  | h cardinal hinduction =>
    cases subsingleton_or_nontrivial G with
    | inl hsubsingleton =>
      let _ := hsubsingleton
      exact inferInstance
    | inr hnontrivial =>
      let _ := hnontrivial
      let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      let square : G →* G := powMonoidHom 2
      obtain ⟨central, _, hunique⟩ := rank_one_two_group_unique_involution hpgroup hrank
      have hcentralSquare : (central : G) ^ 2 = 1 := by
        simpa only [central.property] using pow_orderOf_eq_one (central : G)
      let centralKer : square.ker := ⟨central, hcentralSquare⟩
      have hkerCard : Nat.card square.ker = 2 := by
        apply (Nat.card_eq_two_iff' (1 : square.ker)).mpr
        refine ⟨centralKer, ?_, ?_⟩
        · intro heq
          have hone : (central : G) = 1 := congrArg Subtype.val heq
          have horder := central.property
          rw [hone, orderOf_one] at horder
          omega
        · intro element hne
          have hnonidentity : element.val ≠ 1 := fun heq => hne (Subtype.ext heq)
          have hsquare : element.val ^ 2 = 1 := element.property
          let involution : Involution G := ⟨element.val, orderOf_eq_prime hsquare hnonidentity⟩
          apply Subtype.ext
          exact congrArg (fun involution : Involution G => involution.val) (hunique involution)
      have hindex : square.ker.index = Nat.card square.range := by
        rw [Subgroup.index_eq_card]
        exact Nat.card_congr (QuotientGroup.quotientKerEquivRange square).toEquiv
      have hcardProduct : Nat.card square.range * 2 = Nat.card G := by
        rw [← hkerCard, ← hindex]
        exact square.ker.index_mul_card
      have hrangeLt : Nat.card square.range < cardinal := by
        have hpositive : 0 < Nat.card square.range := Nat.card_pos
        omega
      have hrangeCyclic : IsCyclic square.range := hinduction (Nat.card square.range) hrangeLt
        square.range (hpgroup.to_subgroup square.range)
        (subgroup_no_commuting_distinct_involutions square.range hrank) rfl
      let _ := hrangeCyclic
      by_cases hrangeOne : Nat.card square.range = 1
      · have hgroupTwo : Nat.card G = 2 := by rw [hrangeOne, one_mul] at hcardProduct; exact hcardProduct.symm
        exact isCyclic_of_prime_card hgroupTwo
      · obtain ⟨generator, hgeneratorOrder⟩ :=
          isCyclic_iff_exists_orderOf_eq_natCard.mp hrangeCyclic
        obtain ⟨element, hroot⟩ := generator.property
        have hrootSquare : element ^ 2 = generator.val := hroot
        have hnonidentity : element ≠ 1 := by
          intro hone
          have hgeneratorOne : generator = 1 := by
            apply Subtype.ext
            rw [← hrootSquare, hone, one_pow]
            rfl
          rw [hgeneratorOne, orderOf_one] at hgeneratorOrder
          exact hrangeOne hgeneratorOrder.symm
        have horderDiv : 2 ∣ orderOf element := hpgroup.dvd_orderOf hnonidentity
        have hrootOrder : orderOf element / 2 = Nat.card square.range := by
          rw [← orderOf_pow_of_dvd (by decide : 2 ≠ 0) horderDiv, hrootSquare,
            Subgroup.orderOf_coe, hgeneratorOrder]
        have horder : orderOf element = Nat.card G := by
          calc
            orderOf element = orderOf element / 2 * 2 := (Nat.div_mul_cancel horderDiv).symm
            _ = Nat.card square.range * 2 := by rw [hrootOrder]
            _ = Nat.card G := hcardProduct
        exact isCyclic_of_orderOf_eq_card element horder

end CFSG.DisconnectedInvolutionGraph.Helpers
