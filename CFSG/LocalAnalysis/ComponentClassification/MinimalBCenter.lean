module

public import CFSG.LocalAnalysis.ComponentClassification.OddKernelBObstruction

public section

open CFSG.Open

namespace CFSG.ComponentClassification.MinimalBCenter

theorem quotient_card_lt {G : Type*} [Group G] [Finite G]
    (subgroup : Subgroup G) (hne : subgroup ≠ ⊥) : Nat.card (G ⧸ subgroup) < Nat.card G := by
  have hcardNe : Nat.card subgroup ≠ 1 := fun hone => hne (Subgroup.card_eq_one.mp hone)
  have hcardPos : 0 < Nat.card subgroup := Nat.card_pos
  have hquotientPos : 0 < Nat.card (G ⧸ subgroup) := Nat.card_pos
  rw [subgroup.card_eq_card_quotient_mul_card_subgroup]
  have hcardGt : 1 < Nat.card subgroup := by omega
  exact (Nat.lt_mul_iff_one_lt_right hquotientPos).mpr hcardGt

theorem odd_center {G : Type*} [Group G] [Finite G]
    (hsmaller : ∀ (subgroup : Subgroup G) (_ : subgroup.Normal),
      Nat.card (G ⧸ subgroup) < Nat.card G → CentralTwoBInclusion.Property (G ⧸ subgroup))
    (hfailure : ¬ CentralTwoBInclusion.Property G) : Odd (Nat.card (Subgroup.center G)) := by
  by_contra hnotOdd
  have heven : 2 ∣ Nat.card (Subgroup.center G) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hnotOdd)
  obtain ⟨involution, hinvolution⟩ := exists_prime_orderOf_dvd_card' 2 heven
  let centralTwo := Subgroup.zpowers involution.val
  have hcentral : centralTwo ≤ Subgroup.center G := Subgroup.zpowers_le.mpr involution.property
  have horder : orderOf involution.val = 2 := by
    exact (orderOf_injective (Subgroup.center G).subtype
      (Subgroup.center G).subtype_injective involution).trans hinvolution
  have htwo : IsPGroup 2 centralTwo :=
    IsPGroup.of_card (n := 1) (by
      change Nat.card (Subgroup.zpowers involution.val) = 2 ^ 1
      simpa only [Nat.card_zpowers, pow_one] using horder)
  have hne : centralTwo ≠ ⊥ := by
    intro hbot
    have hone : involution.val = 1 := Subgroup.zpowers_eq_bot.mp hbot
    simp [hone] at horder
  let : centralTwo.Normal := ⟨by
    intro member hmember actor
    rw [Subgroup.mem_center_iff.mp (hcentral hmember) actor]
    simpa only [mul_inv_cancel_right] using hmember⟩
  have hquotient := hsmaller centralTwo inferInstance (quotient_card_lt centralTwo hne)
  apply hfailure
  exact CentralTwoBInclusion.of_central_two_kernel (QuotientGroup.mk' centralTwo)
    (QuotientGroup.mk'_surjective _) (by rwa [QuotientGroup.ker_mk'])
    (by rwa [QuotientGroup.ker_mk']) hquotient

theorem center_eq_bot {G : Type*} [Group G] [Finite G]
    (hsmaller : ∀ (subgroup : Subgroup G) (_ : subgroup.Normal),
      Nat.card (G ⧸ subgroup) < Nat.card G → CentralTwoBInclusion.Property (G ⧸ subgroup))
    (hfailure : ¬ CentralTwoBInclusion.Property G) : Subgroup.center G = ⊥ := by
  have hodd := odd_center hsmaller hfailure
  by_contra hne
  have hquotient := hsmaller (Subgroup.center G) inferInstance
    (quotient_card_lt (Subgroup.center G) hne)
  apply hfailure
  exact OddKernelBObstruction.inclusion_of_central_odd_kernel
    (QuotientGroup.mk' (Subgroup.center G)) (QuotientGroup.mk'_surjective _)
    (by rwa [QuotientGroup.ker_mk']) (by rw [QuotientGroup.ker_mk']) hquotient

end CFSG.ComponentClassification.MinimalBCenter
