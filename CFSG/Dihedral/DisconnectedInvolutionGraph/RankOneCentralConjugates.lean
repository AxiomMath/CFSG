module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneCenterTwo

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem rank_one_two_central_coset_conjugates
    (hpgroup : IsPGroup 2 G) (hrank : NoCommutingDistinctInvolutions G)
    (hnonabelian : ∃ first second : G, first * second ≠ second * first)
    (element : G)
    (hcosetCentral : QuotientGroup.mk' (Subgroup.center G) element ∈
      Subgroup.center (G ⧸ Subgroup.center G))
    (hcosetOrder : orderOf (QuotientGroup.mk' (Subgroup.center G) element) = 2)
    (actor : G) : actor * element * actor⁻¹ = element ∨
      actor * element * actor⁻¹ = element⁻¹ := by
  classical
  let quotient := QuotientGroup.mk' (Subgroup.center G)
  have hcenterCard := rank_one_two_nonabelian_center_card_two hpgroup hrank hnonabelian
  have hcenterGenerates := rank_one_two_central_coset_square_generates_center
    hpgroup hrank element hcosetOrder
  have hsquareCentral : element ^ 2 ∈ Subgroup.center G := by
    rw [← hcenterGenerates]
    exact Subgroup.mem_zpowers _
  have hnoncentral : element ∉ Subgroup.center G := by
    intro hmem
    have hone := (QuotientGroup.eq_one_iff element).mpr hmem
    change quotient element = 1 at hone
    rw [hone, orderOf_one] at hcosetOrder
    omega
  have hsquareNe : element ^ 2 ≠ 1 := by
    intro hone
    have htrivial : Subgroup.center G = ⊥ := by
      rw [← hcenterGenerates, hone, Subgroup.zpowers_one_eq_bot]
    rw [htrivial, Subgroup.card_bot] at hcenterCard
    omega
  have hfourth : element ^ 4 = 1 := by
    have hsquareOrder : orderOf (element ^ 2) = 2 := by
      rw [← Nat.card_zpowers, hcenterGenerates, hcenterCard]
    have hsquarePower := pow_orderOf_eq_one (element ^ 2)
    rw [hsquareOrder] at hsquarePower
    simpa only [show (4 : ℕ) = 2 * 2 from rfl, pow_mul] using hsquarePower
  let difference := element⁻¹ * (actor * element * actor⁻¹)
  have hdifferenceCentral : difference ∈ Subgroup.center G := by
    apply (QuotientGroup.eq_one_iff difference).mp
    change quotient difference = 1
    have hcommute := Subgroup.mem_center_iff.mp hcosetCentral (quotient actor)
    change quotient actor * quotient element = quotient element * quotient actor at hcommute
    simp only [difference, map_mul, map_inv]
    rw [hcommute]
    group
  let squareInside : Subgroup.center G := ⟨element ^ 2, hsquareCentral⟩
  let differenceInside : Subgroup.center G := ⟨difference, hdifferenceCentral⟩
  have hsquareInsideNe : squareInside ≠ 1 := by
    intro heq
    exact hsquareNe (congrArg Subtype.val heq)
  have hdifferenceCases : difference = 1 ∨ difference = element ^ 2 := by
    by_cases hone : differenceInside = 1
    · exact Or.inl (congrArg Subtype.val hone)
    · obtain ⟨unique, _, hunique⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center G)).mp hcenterCard
      exact Or.inr (congrArg Subtype.val ((hunique differenceInside hone).trans
        (hunique squareInside hsquareInsideNe).symm))
  rcases hdifferenceCases with hone | hsquare
  · left
    have heq := congrArg (fun other => element * other) hone
    simpa only [difference, mul_inv_cancel_left, mul_one] using heq
  · right
    have heq := congrArg (fun other => element * other) hsquare
    have hcube : element * element ^ 2 = element⁻¹ := by
      apply mul_right_cancel (b := element)
      calc
        element * element ^ 2 * element = element ^ 4 := by group
        _ = 1 := hfourth
        _ = element⁻¹ * element := (inv_mul_cancel element).symm
    simpa only [difference, mul_inv_cancel_left, hcube] using heq

end CFSG.DisconnectedInvolutionGraph.Helpers
