module

public import CFSG.CharacterTheory.TwoRankLowerBound.CentralSectionSwitch
public import CFSG.CharacterTheory.TwoRankLowerBound.BlockSectionMask

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem two_primary_regular_odd_iff {G : Type*} [Group G]
    (primary regular : G) (exponent : ℕ)
    (hprimary : orderOf primary ∣ 2 ^ exponent)
    (hregular : Nat.Coprime 2 (orderOf regular)) (hcommute : Commute primary regular) :
    Odd (orderOf (primary * regular)) ↔ primary = 1 := by
  have hcoprime : Nat.Coprime (orderOf primary) (orderOf regular) :=
    (hregular.pow_left exponent).of_dvd_left hprimary
  rw [hcommute.orderOf_mul_eq_mul_orderOf_of_coprime hcoprime]
  constructor
  · intro hodd
    have hoddPrimary := hodd.of_dvd_nat (dvd_mul_right (orderOf primary) (orderOf regular))
    exact orderOf_eq_one_iff.mp ((hoddPrimary.coprime_two_right.pow_right exponent).eq_one_of_dvd hprimary)
  · intro hequal
    rw [hequal, orderOf_one, one_mul]
    exact Nat.coprime_two_left.mp hregular

theorem two_primary_central_involution_product_order {G : Type*} [Group G]
    (primary involution : G) (exponent : ℕ)
    (hprimary : orderOf primary ∣ 2 ^ exponent)
    (hcentral : involution ∈ Subgroup.center G) (horder : orderOf involution = 2) :
    orderOf (primary * involution) ∣ 2 ^ (exponent + 1) := by
  have hcommute : Commute primary involution := Subgroup.mem_center_iff.mp hcentral primary
  have hdvd := hcommute.orderOf_mul_dvd_mul_orderOf
  rw [horder] at hdvd
  simpa only [Nat.pow_succ] using hdvd.trans (Nat.mul_dvd_mul hprimary (dvd_refl 2))

theorem centralInvolutionSections_primary_iff {G : Type*} [Group G]
    (involution : G) (hcentral : involution ∈ Subgroup.center G) (horder : orderOf involution = 2)
    (primary regular : G) (exponent : ℕ)
    (hprimary : orderOf primary ∣ 2 ^ exponent)
    (hregular : Nat.Coprime 2 (orderOf regular)) (hcommute : Commute primary regular) :
    primary * regular ∈ centralInvolutionSections involution ↔ primary = 1 ∨ primary = involution := by
  have hregularCommute : Commute regular involution := Subgroup.mem_center_iff.mp hcentral regular
  have hshiftCommute : Commute (primary * involution) regular := hcommute.mul_left hregularCommute.symm
  have hshiftProduct : primary * regular * involution = (primary * involution) * regular := by
    rw [mul_assoc, hregularCommute.eq, ← mul_assoc]
  have hinverse : involution⁻¹ = involution := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two, horder] using pow_orderOf_eq_one involution
  change Odd (orderOf (primary * regular)) ∨ Odd (orderOf (primary * regular * involution)) ↔ _
  rw [two_primary_regular_odd_iff primary regular exponent hprimary hregular hcommute,
    hshiftProduct,
    two_primary_regular_odd_iff (primary * involution) regular (exponent + 1)
      (two_primary_central_involution_product_order primary involution exponent hprimary hcentral horder)
      hregular hshiftCommute,
    mul_eq_one_iff_eq_inv, hinverse]

theorem centralInvolutionSections_primeSectionUnion {G : Type*} [Group G]
    (involution : G) (hcentral : involution ∈ Subgroup.center G) (horder : orderOf involution = 2) :
    primeSectionUnion 2 (centralInvolutionSections involution) := by
  intro leftPrimary rightPrimary leftRegular rightRegular leftExponent rightExponent
    hleftPrimary hrightPrimary hleftRegular hrightRegular hleftCommute hrightCommute hconjugate
  rw [centralInvolutionSections_primary_iff involution hcentral horder leftPrimary leftRegular
      leftExponent hleftPrimary hleftRegular hleftCommute,
    centralInvolutionSections_primary_iff involution hcentral horder rightPrimary rightRegular
      rightExponent hrightPrimary hrightRegular hrightCommute]
  have heqone : leftPrimary = 1 ↔ rightPrimary = 1 := by
    constructor
    · intro hequal
      exact isConj_one_right.mp (hequal ▸ hconjugate)
    · intro hequal
      exact isConj_one_left.mp (hequal ▸ hconjugate)
  have heqinvolution : leftPrimary = involution ↔ rightPrimary = involution := by
    constructor
    · intro hequal
      have heq := (hequal ▸ hconjugate).eq_of_left_mem_center hcentral
      exact heq.symm
    · intro hequal
      exact (hequal ▸ hconjugate).eq_of_right_mem_center hcentral
  exact or_congr heqone heqinvolution

theorem oddOrderElements_primeSectionUnion {G : Type*} [Group G] :
    primeSectionUnion 2 {element : G | Odd (orderOf element)} := by
  intro leftPrimary rightPrimary leftRegular rightRegular leftExponent rightExponent
    hleftPrimary hrightPrimary hleftRegular hrightRegular hleftCommute hrightCommute hconjugate
  change Odd (orderOf (leftPrimary * leftRegular)) ↔ Odd (orderOf (rightPrimary * rightRegular))
  rw [two_primary_regular_odd_iff leftPrimary leftRegular leftExponent hleftPrimary hleftRegular hleftCommute,
    two_primary_regular_odd_iff rightPrimary rightRegular rightExponent hrightPrimary hrightRegular hrightCommute]
  constructor
  · intro hequal
    exact isConj_one_right.mp (hequal ▸ hconjugate)
  · intro hequal
    exact isConj_one_left.mp (hequal ▸ hconjugate)

end CFSG.TwoRankLowerBound.Helpers
