module

public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Blueprint CFSG.Sporadic.Mathieu

set_option maxRecDepth 100000 in
theorem m22_ab_pow : (m22gA * m22gB) ^ 11 = 1 := by decide

set_option maxRecDepth 100000 in
theorem m22_ab_ne : m22gA * m22gB ≠ 1 := by decide

set_option maxRecDepth 100000 in
theorem m24_ab_pow : (m24gA * m24gB) ^ 23 = 1 := by decide

set_option maxRecDepth 100000 in
theorem m24_ab_ne : m24gA * m24gB ≠ 1 := by decide

theorem eleven_dvd_card_nativeM22 : 11 ∣ Nat.card NativeSporadic.M22 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have h1 : (m22a * m22b) ^ 11 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_mul]
    exact m22_ab_pow
  have h2 : m22a * m22b ≠ 1 := by
    intro h
    have h' := congrArg Subtype.val h
    rw [Subgroup.coe_mul, Subgroup.coe_one] at h'
    exact m22_ab_ne h'
  have h3 := orderOf_eq_prime h1 h2
  have := orderOf_dvd_natCard (m22a * m22b)
  rwa [h3] at this

theorem twentythree_dvd_card_nativeM24 : 23 ∣ Nat.card NativeSporadic.M24 := by
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  have h1 : (m24a * m24b) ^ 23 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_mul]
    exact m24_ab_pow
  have h2 : m24a * m24b ≠ 1 := by
    intro h
    have h' := congrArg Subtype.val h
    rw [Subgroup.coe_mul, Subgroup.coe_one] at h'
    exact m24_ab_ne h'
  have h3 := orderOf_eq_prime h1 h2
  have := orderOf_dvd_natCard (m24a * m24b)
  rwa [h3] at this

end CFSG.CGT.Timmesfeld75
