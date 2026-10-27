module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.AnisoCube

theorem dvd_sq_sub_add_one_of_orderOf_eq_six {p q : ℕ} (hp : p.Prime)
    (h : orderOf ((q : ℕ) : ZMod p) = 6) : p ∣ q ^ 2 - q + 1 ∧ p ≠ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  have hx6 : ((q : ℕ) : ZMod p) ^ 6 = 1 := by rw [← h]; exact pow_orderOf_eq_one _
  have hx3ne : ((q : ℕ) : ZMod p) ^ 3 ≠ 1 := by
    intro h3
    have hd := orderOf_dvd_of_pow_eq_one h3
    rw [h] at hd
    norm_num at hd
  have hx3 : ((q : ℕ) : ZMod p) ^ 3 + 1 = 0 := by
    have hfac : (((q : ℕ) : ZMod p) ^ 3 - 1) * (((q : ℕ) : ZMod p) ^ 3 + 1) = 0 := by
      linear_combination hx6
    exact (mul_eq_zero.1 hfac).resolve_left (sub_ne_zero.2 hx3ne)
  have hx1ne : ((q : ℕ) : ZMod p) + 1 ≠ 0 := by
    intro h1
    have hneg : ((q : ℕ) : ZMod p) = -1 := eq_neg_of_add_eq_zero_left h1
    have hsq : ((q : ℕ) : ZMod p) ^ 2 = 1 := by rw [hneg]; norm_num
    have hd := orderOf_dvd_of_pow_eq_one hsq
    rw [h] at hd
    norm_num at hd
  refine ⟨?_, ?_⟩
  ·
    have hq : ((q : ℕ) : ZMod p) ^ 2 - ((q : ℕ) : ZMod p) + 1 = 0 := by
      have hfac : (((q : ℕ) : ZMod p) + 1) * (((q : ℕ) : ZMod p) ^ 2 - ((q : ℕ) : ZMod p) + 1)
          = 0 := by
        linear_combination hx3
      exact (mul_eq_zero.1 hfac).resolve_left hx1ne
    have hle : q ≤ q ^ 2 := Nat.le_self_pow two_ne_zero q
    refine (ZMod.natCast_eq_zero_iff (q ^ 2 - q + 1) p).1 ?_
    rw [Nat.cast_add, Nat.cast_sub hle, Nat.cast_pow, Nat.cast_one]
    exact hq
  ·
    rintro rfl
    have hF : ((q : ℕ) : ZMod 3) ^ 3 = ((q : ℕ) : ZMod 3) := ZMod.pow_card _
    have h6 : ((q : ℕ) : ZMod 3) ^ 6 = (((q : ℕ) : ZMod 3) ^ 3) ^ 2 := by ring
    rw [hF] at h6
    have hsq : ((q : ℕ) : ZMod 3) ^ 2 = 1 := h6.symm.trans hx6
    have hd := orderOf_dvd_of_pow_eq_one hsq
    rw [h] at hd
    norm_num at hd

end CFSG.HardMathSupport.Foote.Coordinator.AnisoCube
