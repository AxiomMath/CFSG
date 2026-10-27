module

public import CFSG.Quasithin.Background.B1Offender

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81

open CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem commute_of_isPGroup_of_transvection [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {t : MulAut V} (ht : IsTransvection t) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    {R : Subgroup (MulAut V)} (hR : IsPGroup r R) (htR : ∀ y ∈ R, t * y * t⁻¹ ∈ R) :
    ∀ y ∈ R, t * y = y * t := by
  intro y hy
  obtain ⟨ht1, w, htw⟩ := ht
  have htt : t * t = 1 := B1.tv_sq hV htw ht1
  obtain ⟨x, hx⟩ : ∃ x, x = y * (t * y⁻¹ * t⁻¹) := ⟨_, rfl⟩
  have hxR : x ∈ R := hx ▸ R.mul_mem hy (htR _ (R.inv_mem hy))
  have htx : t * x * t⁻¹ = x⁻¹ := by
    have e1 : t * x * t⁻¹ = t * y * t⁻¹ * ((t * t) * y⁻¹ * (t * t)⁻¹) := by rw [hx]; group
    have e2 : x⁻¹ = t * y * t⁻¹ * y⁻¹ := by rw [hx]; group
    rw [e1, e2, htt]
    group
  obtain ⟨k, hk⟩ := hR ⟨x, hxR⟩
  have hxk : x ^ (r ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hodd : Odd (r ^ k) := (hr.odd_of_ne_two hr2).pow
  have hx1 : x = 1 := by
    by_contra hx1
    have hx3 : x ^ 3 = 1 := (B1.inverted_by_transvection hV htw ht1 hodd hxk hx1 htx).2.2.2
    have h3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    have hrk : orderOf x ∣ r ^ k := orderOf_dvd_of_pow_eq_one hxk
    have hcop : Nat.Coprime 3 (r ^ k) :=
      Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_three hr).mpr (Ne.symm hr3))
    exact hx1 (orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left h3) hrk))
  have hyt : y * (t * y⁻¹ * t⁻¹) = 1 := hx ▸ hx1
  calc t * y = (y * (t * y⁻¹ * t⁻¹))⁻¹ * y * t := by group
    _ = y * t := by rw [hyt, inv_one, one_mul]

theorem isFFStarOffender_zpowers_of_transvection [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {X : Subgroup (MulAut V)} {t : MulAut V} (htX : t ∈ X) (ht : IsTransvection t) :
    IsFFStarOffender X (Subgroup.zpowers t) := by
  obtain ⟨ht1, w, htw⟩ := ht
  have hsq : t ^ 2 = 1 := by rw [pow_two]; exact B1.tv_sq hV htw ht1
  have hcard : Nat.card (Subgroup.zpowers t) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hsq ht1]
  refine ⟨Subgroup.zpowers_le.2 htX, fun h => ht1 (Subgroup.zpowers_eq_bot.1 h),
    B1.isElemAbelian2_zpowers_tv hV ht1 htw, fun B hB => ?_⟩
  have hdvd : Nat.card B ∣ 2 := hcard ▸ Subgroup.card_dvd_of_le hB
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · rw [Subgroup.eq_bot_of_card_eq B h1, Subgroup.card_bot, one_mul, hcard,
      ← B1.card_eq_two_mul_fixV_of_tv hV ht1 htw]
    exact Nat.card_le_card_of_injective _ Subtype.val_injective
  · have hBt : B = Subgroup.zpowers t := Subgroup.eq_of_le_of_card_ge hB (by rw [hcard, h2])
    rw [hBt]

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81
