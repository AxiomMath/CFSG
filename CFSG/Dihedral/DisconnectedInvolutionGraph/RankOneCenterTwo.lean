module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneEqualSquares

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem rank_one_two_nonabelian_center_card_two
    (hpgroup : IsPGroup 2 G) (hrank : NoCommutingDistinctInvolutions G)
    (hnonabelian : ∃ first second : G, first * second ≠ second * first) :
    Nat.card (Subgroup.center G) = 2 := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨first, second, hcosetCentral, _, hequalSquare, hcenterGenerates, hnoncommute⟩ :=
    rank_one_two_exists_noncommuting_equal_squares hpgroup hrank hnonabelian
  let other := second⁻¹
  let quotient := QuotientGroup.mk' (Subgroup.center G)
  let central := (first * other)⁻¹ * (other * first)
  have hcentral : central ∈ Subgroup.center G := by
    apply (QuotientGroup.eq_one_iff central).mp
    change quotient central = 1
    have hcommuteQuotient : quotient other * quotient first = quotient first * quotient other :=
      Subgroup.mem_center_iff.mp hcosetCentral (quotient other)
    change quotient ((first * other)⁻¹ * (other * first)) = 1
    rw [map_mul, map_inv, map_mul, map_mul, hcommuteQuotient, inv_mul_cancel]
  have hcommutation : other * first = first * other * central := by
    change other * first = first * other * ((first * other)⁻¹ * (other * first))
    group
  have hcentralNe : central ≠ 1 := by
    intro hone
    have hotherCommutes : first * other = other * first := by
      rw [hone, mul_one] at hcommutation
      exact hcommutation.symm
    have hsecondCommutes : Commute first second := by
      have hcommutes : Commute first other := hotherCommutes
      simpa only [other, inv_inv] using hcommutes.inv_right
    exact hnoncommute hsecondCommutes
  have hotherSquare : other ^ 2 = (first ^ 2)⁻¹ := by
    change (second⁻¹) ^ 2 = (first ^ 2)⁻¹
    rw [inv_pow, hequalSquare]
  have hfirstSquareCentral : first ^ 2 ∈ Subgroup.center G := by
    rw [← hcenterGenerates]
    exact Subgroup.mem_zpowers _
  have hotherSquareCentral : other ^ 2 ∈ Subgroup.center G := by
    rw [hotherSquare]
    exact (Subgroup.center G).inv_mem hfirstSquareCentral
  have hconjugation : first⁻¹ * other * first = other * central := by
    have heq := congrArg (fun element : G => first⁻¹ * element) hcommutation
    simpa only [mul_assoc, inv_mul_cancel_left] using heq
  have hcentralSquare : central ^ 2 = 1 := by
    have hleftSquare : (first⁻¹ * other * first) ^ 2 = other ^ 2 := by
      calc
        (first⁻¹ * other * first) ^ 2 = first⁻¹ * other ^ 2 * first := by
          simp only [pow_two, mul_assoc, mul_inv_cancel_left]
        _ = other ^ 2 := by
          rw [Subgroup.mem_center_iff.mp hotherSquareCentral first⁻¹,
            mul_assoc, inv_mul_cancel, mul_one]
    have hotherCommutesCentral : Commute other central :=
      Subgroup.mem_center_iff.mp hcentral other
    rw [hconjugation, hotherCommutesCentral.mul_pow] at hleftSquare
    exact mul_left_cancel (hleftSquare.trans (mul_one (other ^ 2)).symm)
  have hproductSquare : (first * other) ^ 2 = central := by
    have hcentralCommutesOther : central * other = other * central :=
      (Subgroup.mem_center_iff.mp hcentral other).symm
    calc
      (first * other) ^ 2 = first * (other * first) * other := by simp only [pow_two, mul_assoc]
      _ = first * (first * other * central) * other := by rw [hcommutation]
      _ = first ^ 2 * other ^ 2 * central := by
        simp only [pow_two, mul_assoc]
        rw [hcentralCommutesOther]
      _ = central := by rw [hotherSquare, mul_inv_cancel, one_mul]
  have hproductFourth : (first * other) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hproductSquare, hcentralSquare]
  have hproductOrder : orderOf (first * other) = 4 := by
    simpa only [show (2 : ℕ) ^ 1 = 2 from rfl, show (2 : ℕ) ^ (1 + 1) = 4 from rfl] using
      (orderOf_eq_prime_pow (p := 2) (n := 1) (hproductSquare ▸ hcentralNe) hproductFourth)
  have hproductNoncentral : first * other ∉ Subgroup.center G := by
    intro hmem
    have hcomm : first * (first * other) = (first * other) * first :=
      Subgroup.mem_center_iff.mp hmem first
    have hotherComm : first * other = other * first :=
      mul_left_cancel (by simpa only [mul_assoc] using hcomm)
    have hsecondComm : Commute first second := by
      have hcommute : Commute first other := hotherComm
      simpa only [other, inv_inv] using hcommute.inv_right
    exact hnoncommute hsecondComm
  have hcenterLt : Nat.card (Subgroup.center G) < 4 :=
    hproductOrder ▸ rank_one_two_center_card_lt_order hpgroup hrank (first * other) hproductNoncentral
  have hcenterEven : 2 ∣ Nat.card (Subgroup.center G) := by
    have hdiv := (Subgroup.center G).orderOf_dvd_natCard hcentral
    rw [orderOf_eq_prime hcentralSquare hcentralNe] at hdiv
    exact hdiv
  have hcenterPositive : 0 < Nat.card (Subgroup.center G) := Nat.card_pos
  omega

end CFSG.DisconnectedInvolutionGraph.Helpers
