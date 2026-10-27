module

public import CFSG.CharacterTheory.TwoRankLowerBound.CentralQuotientPair

public section

open CFSG.Open

namespace CFSG.TwoRankLowerBound.Helpers

theorem noncommuting_equal_square_pair_has_order_four_product (G : Type*) [Group G]
    (left right : G) (hnoncommute : left * right ≠ right * left)
    (hsquares : left ^ 2 = right ^ 2)
    (hcentral : left ^ 2 ∈ Subgroup.center G)
    (hquotient : (QuotientGroup.mk' (Subgroup.center G)) left ∈
      Subgroup.center (G ⧸ Subgroup.center G)) :
    orderOf (left * right⁻¹) = 4 := by
  let inverse := right⁻¹
  let factor := (inverse * left) / (left * inverse)
  have hfactorcentral : factor ∈ Subgroup.center G := by
    apply QuotientGroup.eq_iff_div_mem.mp
    change (QuotientGroup.mk' (Subgroup.center G)) (inverse * left) =
      (QuotientGroup.mk' (Subgroup.center G)) (left * inverse)
    simp only [map_mul]
    exact Subgroup.mem_center_iff.mp hquotient _
  have hcommute : Commute factor (left * inverse) :=
    (Subgroup.mem_center_iff.mp hfactorcentral _).symm
  have hrelation : inverse * left = left * inverse * factor := by
    calc
      inverse * left = factor * (left * inverse) := (div_mul_cancel _ _).symm
      _ = left * inverse * factor := hcommute.eq
  have hfactorne : factor ≠ 1 := by
    intro hone
    have hcommuteinverse : Commute inverse left := by
      change inverse * left = left * inverse
      simpa [hone] using hrelation
    exact hnoncommute (Commute.inv_right_iff.mp hcommuteinverse.symm)
  have hinversesquare : inverse ^ 2 = (left ^ 2)⁻¹ := by
    dsimp [inverse]
    rw [inv_pow, ← hsquares]
  have hinversecentral : inverse ^ 2 ∈ Subgroup.center G := by
    rw [hinversesquare]
    exact Subgroup.inv_mem _ hcentral
  have hconjugate : left⁻¹ * inverse * left = inverse * factor := by
    calc
      left⁻¹ * inverse * left = left⁻¹ * (inverse * left) := by group
      _ = left⁻¹ * (left * inverse * factor) := by rw [hrelation]
      _ = inverse * factor := by group
  have hfactorcommute : Commute inverse factor := Subgroup.mem_center_iff.mp hfactorcentral _
  have hfactorsquare : factor ^ 2 = 1 := by
    have hconjugatesquare : (left⁻¹ * inverse * left) ^ 2 = inverse ^ 2 := by
      have hcentralcommute := Subgroup.mem_center_iff.mp hinversecentral left⁻¹
      calc
        (left⁻¹ * inverse * left) ^ 2 =
            (left⁻¹ * inverse * (left⁻¹)⁻¹) ^ 2 := by rw [inv_inv]
        _ = left⁻¹ * inverse ^ 2 * (left⁻¹)⁻¹ := conj_pow
        _ = left⁻¹ * inverse ^ 2 * left := by rw [inv_inv]
        _ = inverse ^ 2 * left⁻¹ * left := by rw [hcentralcommute]
        _ = inverse ^ 2 := by group
    rw [hconjugate, hfactorcommute.mul_pow] at hconjugatesquare
    exact mul_left_cancel (hconjugatesquare.trans (mul_one _).symm)
  have hproductsquare : (left * inverse) ^ 2 = factor := by
    calc
      (left * inverse) ^ 2 = left * (inverse * left) * inverse := by rw [pow_two]; group
      _ = left * (left * inverse * factor) * inverse := by rw [hrelation]
      _ = left ^ 2 * inverse * factor * inverse := by rw [pow_two]; group
      _ = left ^ 2 * inverse * (factor * inverse) := by group
      _ = left ^ 2 * inverse * (inverse * factor) := by rw [hfactorcommute.eq]
      _ = left ^ 2 * inverse ^ 2 * factor := by rw [pow_two inverse]; group
      _ = factor := by rw [hinversesquare]; group
  change orderOf (left * inverse) = 4
  apply orderOf_eq_prime_pow (p := 2) (n := 1)
  · simpa only [pow_one, hproductsquare] using hfactorne
  · have hfour : (left * inverse) ^ (2 * 2) = 1 := by
      rw [pow_mul, hproductsquare, hfactorsquare]
    exact hfour

theorem center_card_eq_two_of_nonabelian_rank_one_two_group (G : Type*)
    [Group G] [Finite G] (htwogroup : IsPGroup 2 G) (hrank : twoRank G ≤ 1)
    (hnonabelian : ∃ left right : G, left * right ≠ right * left) :
    Nat.card (Subgroup.center G) = 2 := by
  obtain ⟨left, right, hnoncommute, hsquares, hcentergenerator, hquotient⟩ :=
    exists_noncommuting_pair_with_equal_central_squares G htwogroup hrank hnonabelian
  have hsquarecentral : left ^ 2 ∈ Subgroup.center G := by
    rw [← hcentergenerator]
    exact Subgroup.mem_zpowers _
  have hproductorder := noncommuting_equal_square_pair_has_order_four_product G
    left right hnoncommute hsquares hsquarecentral hquotient
  have hproductnoncentral : left * right⁻¹ ∉ Subgroup.center G := by
    intro hcentral
    have hcommute : Commute left (left * right⁻¹) := Subgroup.mem_center_iff.mp hcentral left
    have hrightcommute : Commute left right⁻¹ := by
      apply mul_left_cancel (a := left)
      simpa only [mul_assoc] using hcommute.eq
    exact hnoncommute (Commute.inv_right_iff.mp hrightcommute)
  have hcardlt := center_card_lt_orderOf_of_rank_one_two_group G htwogroup hrank
    (left * right⁻¹) hproductnoncentral
  rw [hproductorder] at hcardlt
  have : Nontrivial G := nontrivial_of_ne (left * right) (right * left) hnoncommute
  have := htwogroup.center_nontrivial
  have hcardgt : 1 < Nat.card (Subgroup.center G) := Finite.one_lt_card_iff_nontrivial.mpr
    (htwogroup.center_nontrivial)
  obtain hcardone | hdivides := (htwogroup.to_subgroup (Subgroup.center G)).card_eq_or_dvd
  · omega
  · omega

end CFSG.TwoRankLowerBound.Helpers
