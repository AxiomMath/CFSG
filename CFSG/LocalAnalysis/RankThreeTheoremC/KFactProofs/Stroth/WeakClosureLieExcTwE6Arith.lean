module

public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross

theorem tw_e6_eclass {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ q)
    (hd : p ∣ CFSG.Open.ordTwistedE6 q) :
    orderOf (q : ZMod p) = 1 ∨ orderOf (q : ZMod p) = 2 ∨ orderOf (q : ZMod p) = 3 ∨
      orderOf (q : ZMod p) = 4 ∨ orderOf (q : ZMod p) = 6 ∨ orderOf (q : ZMod p) = 8 ∨
      orderOf (q : ZMod p) = 10 ∨ orderOf (q : ZMod p) = 12 ∨ orderOf (q : ZMod p) = 18 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq0 : (q : ZMod p) ≠ 0 := fun h => hpq ((ZMod.natCast_eq_zero_iff q p).1 h)
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (fun h => hpq (by simp [h]))
  have hN : p ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
      (q ^ 2 - 1) := by
    have hg : Nat.gcd 3 (q + 1) ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) *
        (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1) := by
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      have h2 : (q' + 1) ^ 2 - 1 = q' * (q' + 2) := by
        have : (q' + 1) ^ 2 = q' * (q' + 2) + 1 := by ring
        omega
      refine Dvd.dvd.mul_left ?_ _
      rw [h2]
      exact (Nat.gcd_dvd_right 3 (q' + 1 + 1)).trans (Dvd.intro_left _ rfl)
    exact hd.trans (by
      unfold CFSG.Open.ordTwistedE6
      exact Nat.div_dvd_of_dvd hg)
  have hcast : ((q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
      (q ^ 2 - 1) : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).2 hN
  have hexp : (q : ZMod p) ^ 36 * ((q : ZMod p) ^ 12 - 1) * ((q : ZMod p) ^ 9 + 1) *
      ((q : ZMod p) ^ 8 - 1) * ((q : ZMod p) ^ 6 - 1) * ((q : ZMod p) ^ 5 + 1) *
      ((q : ZMod p) ^ 2 - 1) = 0 := by
    have h12 : 1 ≤ q ^ 12 := Nat.one_le_pow _ _ hq1
    have h8 : 1 ≤ q ^ 8 := Nat.one_le_pow _ _ hq1
    have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq1
    have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
    push_cast [Nat.cast_sub h12, Nat.cast_sub h8, Nat.cast_sub h6, Nat.cast_sub h2] at hcast
    exact hcast
  set x : ZMod p := (q : ZMod p) with hx
  have hdvd_p : orderOf x ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one hq0
  have he0 : orderOf x ≠ 0 := fun h => by
    rw [h, zero_dvd_iff] at hdvd_p
    have := hp.two_le
    omega
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  have key : ∀ n : ℕ, x ^ n = 1 → orderOf x ∣ n := fun n h => orderOf_dvd_of_pow_eq_one h
  rcases mul_eq_zero.1 hexp with h | h
  · rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · rcases mul_eq_zero.1 h with h | h
          · rcases mul_eq_zero.1 h with h | h
            · exact absurd (pow_eq_zero_iff (by norm_num) |>.1 h) hq0
            ·
              have hd12 := key 12 (sub_eq_zero.1 h)
              have hle := Nat.le_of_dvd (by norm_num) hd12
              interval_cases hc : orderOf x <;> first | omega | simp_all
          ·
            have h18 : x ^ 18 = 1 := by linear_combination (x ^ 9 - 1) * h
            have hd18 := key 18 h18
            have hle := Nat.le_of_dvd (by norm_num) hd18
            have h9 : orderOf x ≠ 9 := by
              intro h9
              have h1 : x ^ 9 = 1 := by rw [← h9]; exact pow_orderOf_eq_one x
              apply h2ne
              linear_combination h - h1
            interval_cases hc : orderOf x <;> first | omega | simp_all
        · have hd8 := key 8 (sub_eq_zero.1 h)
          have hle := Nat.le_of_dvd (by norm_num) hd8
          interval_cases hc : orderOf x <;> first | omega | simp_all
      · have hd6 := key 6 (sub_eq_zero.1 h)
        have hle := Nat.le_of_dvd (by norm_num) hd6
        interval_cases hc : orderOf x <;> first | omega | simp_all
    ·
      have h10 : x ^ 10 = 1 := by linear_combination (x ^ 5 - 1) * h
      have hd10 := key 10 h10
      have hle := Nat.le_of_dvd (by norm_num) hd10
      have h5 : orderOf x ≠ 5 := by
        intro h5
        have h1 : x ^ 5 = 1 := by rw [← h5]; exact pow_orderOf_eq_one x
        apply h2ne
        linear_combination h - h1
      interval_cases hc : orderOf x <;> first | omega | simp_all
  · have hd2 := key 2 (sub_eq_zero.1 h)
    have hle := Nat.le_of_dvd (by norm_num) hd2
    interval_cases hc : orderOf x <;> first | omega | simp_all

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross
