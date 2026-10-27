module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneCyclicCentralizer

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem rank_one_two_exists_order_four_outside_cyclic
    (hpgroup : IsPGroup 2 G) (hrank : NoCommutingDistinctInvolutions G)
    (hnonabelian : ∃ first second : G, first * second ≠ second * first)
    (subgroup : Subgroup G) (hcyclic : IsCyclic subgroup) :
    ∃ element : G, element ∉ subgroup ∧ orderOf element = 4 := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ := hcyclic
  by_contra hmissing
  have hall : ∀ element : G, orderOf element = 4 → element ∈ subgroup := by
    intro element horder
    by_contra houtside
    exact hmissing ⟨element, houtside, horder⟩
  obtain ⟨element, _, hcosetOrder, _⟩ :=
    rank_one_two_exists_central_order_two_coset hpgroup hrank hnonabelian
  have helementOrder := rank_one_two_central_coset_order_four hpgroup hrank hnonabelian
    element hcosetOrder
  have helementMem := hall element helementOrder
  have hcenterCard := rank_one_two_nonabelian_center_card_two hpgroup hrank hnonabelian
  have helementCentral : element ∈ Subgroup.center G := by
    apply Subgroup.mem_center_iff.mpr
    intro actor
    by_cases hcentral : actor ∈ Subgroup.center G
    · exact (Subgroup.mem_center_iff.mp hcentral element).symm
    · have horderGt : 2 < orderOf actor := by
        rw [← hcenterCard]
        exact rank_one_two_center_card_lt_order hpgroup hrank actor hcentral
      obtain ⟨exponent, hexponent⟩ := hpgroup.exists_orderOf_eq_pow actor
      have htwoLe : 2 ≤ exponent := by
        by_contra hsmall
        have hcases : exponent = 0 ∨ exponent = 1 := by omega
        rcases hcases with rfl | rfl
        · rw [pow_zero] at hexponent
          omega
        · rw [pow_one] at hexponent
          omega
      have hfourDvd : 4 ∣ orderOf actor := by
        rw [hexponent]
        exact pow_dvd_pow 2 htwoLe
      let fourth := actor ^ (orderOf actor / 4)
      have hfourthOrder : orderOf fourth = 4 :=
        orderOf_pow_orderOf_div (isOfFinOrder_of_finite actor).orderOf_pos.ne' hfourDvd
      have hfourthMem := hall fourth hfourthOrder
      have hcommute : fourth * element = element * fourth := by
        exact congrArg (fun other : subgroup => other.val)
          (mul_comm' (⟨fourth, hfourthMem⟩ : subgroup) ⟨element, helementMem⟩)
      have hcyclicEq := rank_one_two_commuting_equal_order_zpowers hpgroup hrank
        fourth element hcommute (hfourthOrder.trans helementOrder.symm)
      have helementInFourth : element ∈ Subgroup.zpowers fourth := by
        rw [hcyclicEq]
        exact Subgroup.mem_zpowers element
      have helementInActor : element ∈ Subgroup.zpowers actor :=
        (Subgroup.zpowers_le.mpr (Subgroup.npow_mem_zpowers actor _)) helementInFourth
      obtain ⟨power, rfl⟩ := Subgroup.mem_zpowers_iff.mp helementInActor
      exact (Commute.self_zpow actor power).eq
  have hdiv := (Subgroup.center G).orderOf_dvd_natCard helementCentral
  rw [helementOrder, hcenterCard] at hdiv
  norm_num at hdiv

end CFSG.DisconnectedInvolutionGraph.Helpers
