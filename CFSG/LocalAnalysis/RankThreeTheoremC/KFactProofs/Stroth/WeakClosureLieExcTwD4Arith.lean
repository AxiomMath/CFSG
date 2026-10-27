module

public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross

open CFSG.Open

theorem tw_d4_eclass {p q : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q) (hd : p ∣ ordTrialityD4 q) :
    (orderOf (q : ZMod p) = 1 ∨ orderOf (q : ZMod p) = 2 ∨ orderOf (q : ZMod p) = 3 ∨
      orderOf (q : ZMod p) = 6) ∨ (orderOf (q : ZMod p) = 12 ∧ p ∣ q ^ 4 - q ^ 2 + 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq0 : (q : ZMod p) ≠ 0 := fun h => hpq ((ZMod.natCast_eq_zero_iff q p).1 h)
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (fun h => hpq (by simp [h]))
  have hcast : ((ordTrialityD4 q : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).2 hd
  have hexp : (q : ZMod p) ^ 12 * ((q : ZMod p) ^ 8 + (q : ZMod p) ^ 4 + 1) *
      ((q : ZMod p) ^ 6 - 1) * ((q : ZMod p) ^ 2 - 1) = 0 := by
    have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq1
    have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
    unfold ordTrialityD4 at hcast
    push_cast [Nat.cast_sub h6, Nat.cast_sub h2] at hcast
    exact hcast
  set x : ZMod p := (q : ZMod p) with hx
  have hdvd_p : orderOf x ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one hq0
  have he0 : orderOf x ≠ 0 := fun h => by
    rw [h, zero_dvd_iff] at hdvd_p
    have := hp.two_le
    omega
  have hE : orderOf x = 1 ∨ orderOf x = 2 ∨ orderOf x = 3 ∨ orderOf x = 6 ∨ orderOf x = 12 := by
    rcases mul_eq_zero.1 hexp with h | h
    · rcases mul_eq_zero.1 h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd (pow_eq_zero_iff (by norm_num) |>.1 h) hq0
        ·
          have h12 : x ^ 12 = 1 := by linear_combination (x ^ 4 - 1) * h
          have hd12 : orderOf x ∣ 12 := orderOf_dvd_of_pow_eq_one h12
          have hle := Nat.le_of_dvd (by norm_num) hd12
          have h4 : orderOf x ≠ 4 := by
            intro h4
            have hx4 : x ^ 4 = 1 := by rw [← h4]; exact pow_orderOf_eq_one x
            have h3 : (3 : ZMod p) = 0 := by linear_combination h - (x ^ 4 + 2) * hx4
            have : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h3
            rw [ZMod.natCast_eq_zero_iff] at this
            have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 this
            subst hp3
            rw [h4] at hdvd_p
            omega
          interval_cases hc : orderOf x <;> first | omega | simp_all
      · have hx6 : x ^ 6 = 1 := sub_eq_zero.1 h
        have hd6 : orderOf x ∣ 6 := orderOf_dvd_of_pow_eq_one hx6
        have hle := Nat.le_of_dvd (by norm_num) hd6
        interval_cases hc : orderOf x <;> first | omega | simp_all
    · have hx2 : x ^ 2 = 1 := sub_eq_zero.1 h
      have hd2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
      have hle := Nat.le_of_dvd (by norm_num) hd2
      interval_cases hc : orderOf x <;> first | omega | simp_all
  by_cases h12 : orderOf x = 12
  · refine Or.inr ⟨h12, ?_⟩
    have hx12 : x ^ 12 = 1 := by rw [← h12]; exact pow_orderOf_eq_one x
    have hne6 : x ^ 6 - 1 ≠ 0 := by
      intro h
      have := orderOf_dvd_of_pow_eq_one (sub_eq_zero.1 h)
      rw [h12] at this
      omega
    have hne2 : x ^ 2 + 1 ≠ 0 := by
      intro h
      have hx4 : x ^ 4 = 1 := by linear_combination (x ^ 2 - 1) * h
      have := orderOf_dvd_of_pow_eq_one hx4
      rw [h12] at this
      omega
    have hprod : (x ^ 6 - 1) * (x ^ 2 + 1) * (x ^ 4 - x ^ 2 + 1) = 0 := by
      linear_combination hx12
    have hfin : x ^ 4 - x ^ 2 + 1 = 0 := by
      rcases mul_eq_zero.1 hprod with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd h hne6
        · exact absurd h hne2
      · exact h
    have hle : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right hq1 (by norm_num)
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast [Nat.cast_sub hle]
    exact hfin
  · refine Or.inl ?_
    rcases hE with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · exact absurd h h12

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross
