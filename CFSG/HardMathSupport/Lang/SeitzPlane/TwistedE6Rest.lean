module

public import CFSG.HardMathSupport.Lang.SeitzPlane.TwistedE6Split
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTwistedE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSevenClasses

public section

namespace CFSG.HardMathSupport.Lang.SeitzPlane

open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar TauCeti

theorem degCountTw_orderOf_le_two_of_not_dvd {p n : ℕ} (hp : p.Prime)
    (h₁ : ¬ p ∣ n ^ 2 - 1) (h₂ : ¬ p ∣ n ^ 2 - n + 1) :
    degCountTw (orderOf (n : ZMod p)) ≤ 2 := by
  have := Fact.mk hp
  by_contra hc
  have hcases := degCountTw_ge_three (e := orderOf (n : ZMod p)) (by omega)
  have hn1 : 1 ≤ n ^ 2 := by
    rcases Nat.eq_zero_or_pos (n ^ 2) with h | h
    · rw [h] at h₁
      simp at h₁
    · exact h
  have hle : n ≤ n ^ 2 := by
    rw [pow_two]
    exact Nat.le_mul_self n
  have e2 : ((n ^ 2 - 1 : ℕ) : ZMod p) = (n : ZMod p) ^ 2 - 1 := by
    rw [Nat.cast_sub hn1, Nat.cast_pow, Nat.cast_one]
  have e3 : ((n ^ 2 - n + 1 : ℕ) : ZMod p) = (n : ZMod p) ^ 2 - (n : ZMod p) + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hle, Nat.cast_pow, Nat.cast_one]
  have hcast : ∀ m : ℕ, ((m : ℕ) : ZMod p) = 0 ↔ p ∣ m := fun m =>
    CharP.cast_eq_zero_iff (ZMod p) p m
  rcases hcases with he | he | he
  · have hx1 : (n : ZMod p) = 1 := orderOf_eq_one_iff.mp he
    exact h₁ ((hcast _).mp (by rw [e2, hx1]; norm_num))
  · have hx2 : (n : ZMod p) ^ 2 = 1 := by
      have := pow_orderOf_eq_one (n : ZMod p)
      rwa [he] at this
    exact h₁ ((hcast _).mp (by rw [e2, hx2, sub_self]))
  · have hx6 : (n : ZMod p) ^ 6 = 1 := by
      have := pow_orderOf_eq_one (n : ZMod p)
      rwa [he] at this
    have hy : ((n : ZMod p) ^ 3) ^ 2 = 1 := by
      rw [← hx6]
      ring
    have hfac : ((n : ZMod p) ^ 3 - 1) * ((n : ZMod p) ^ 3 + 1) = 0 := by
      linear_combination hy
    rcases mul_eq_zero.mp hfac with h | h
    · have h3 : (n : ZMod p) ^ 3 = 1 := sub_eq_zero.mp h
      have hd := orderOf_dvd_of_pow_eq_one h3
      rw [he] at hd
      norm_num at hd
    · have hfac2 : ((n : ZMod p) + 1) * ((n : ZMod p) ^ 2 - (n : ZMod p) + 1) = 0 := by
        linear_combination h
      rcases mul_eq_zero.mp hfac2 with h' | h'
      · have hneg : (n : ZMod p) = -1 := eq_neg_of_add_eq_zero_left h'
        have hsq : (n : ZMod p) ^ 2 = 1 := by rw [hneg]; exact neg_one_sq
        have hd := orderOf_dvd_of_pow_eq_one hsq
        rw [he] at hd
        norm_num at hd
      · exact h₂ ((hcast _).mp (by rw [e3]; exact h'))

section Cert

theorem excPlaneTwistedE6Rest : ExcPlaneTwistedE6Rest := by
  unfold ExcPlaneTwistedE6Rest ExcParabolicPlaneOn
  rintro ⟨d, hv⟩ p hp _ hpd _ ⟨q, hd, h₁, h₂⟩ hr
  subst hd
  have hpq : p ≠ q.p := by
    have h := hpd
    rw [TauCeti.LieTypeIndex.characteristic_twistedE6] at h
    exact h
  have hcnt := degCountTw_orderOf_le_two_of_not_dvd (n := q.card) hp h₁ h₂
  rcases Nat.lt_or_ge (degCountTw (orderOf ((q.card : ℕ) : ZMod p))) 2 with h | h
  · exact (hr (rankLE1_cat_twistedE6 q hv hp hpq (by omega)).rankLE2).elim
  · have h2 : degCountTw (orderOf ((q.card : ℕ) : ZMod p)) = 2 := by omega
    exact (hr (rankLE2_cat_twistedE6 q hv hp h2)).elim

end Cert

end CFSG.HardMathSupport.Lang.SeitzPlane

end
