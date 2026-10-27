module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65

open QuaternionGroup Subgroup

section Q16

variable {X : Type} [Group X]

private theorem conj_a_a (k i : ZMod (2 * 4)) :
    (a k : QuaternionGroup 4) * a i * (a k)⁻¹ = a i := by
  show a k * a i * a (-k) = a i
  rw [a_mul_a, a_mul_a]
  congr 1
  ring

private theorem conj_xa_a (k i : ZMod (2 * 4)) :
    (xa k : QuaternionGroup 4) * a i * (xa k)⁻¹ = a (-i) := by
  have h2n : (2 * (4 : ℕ) : ZMod (2 * 4)) = 0 := by decide
  show xa k * a i * xa (((4 : ℕ) : ZMod (2 * 4)) + k) = a (-i)
  rw [xa_mul_a, xa_mul_xa]
  congr 1
  push_cast at h2n ⊢
  linear_combination h2n

private theorem exists_a_of_order_eight (e : X ≃* QuaternionGroup 4) {x : X} (hx : orderOf x = 8) :
    ∃ i : ZMod (2 * 4), e x = a i := by
  have hq : orderOf (e x) = 8 := by rw [MulEquiv.orderOf_eq]; exact hx
  rcases hcase : e x with i | i
  · exact ⟨i, rfl⟩
  · rw [hcase, orderOf_xa] at hq
    omega

theorem q16_conj_gen (e : X ≃* QuaternionGroup 4) {x : X} (hx : orderOf x = 8) (y : X) :
    y * x * y⁻¹ = x ∨ y * x * y⁻¹ = x⁻¹ := by
  obtain ⟨i, hi⟩ := exists_a_of_order_eight e hx
  have hconj : e (y * x * y⁻¹) = e y * a i * (e y)⁻¹ := by rw [map_mul, map_mul, map_inv, hi]
  rcases hy : e y with k | k
  · left
    apply e.injective
    rw [hconj, hy, conj_a_a, hi]
  · right
    apply e.injective
    rw [hconj, hy, conj_xa_a, map_inv, hi]
    rfl

theorem q16_comm_mem_zpowers (e : X ≃* QuaternionGroup 4) {x : X} (hx : orderOf x = 8) {y : X}
    (hy : y * x = x * y) : y ∈ zpowers x := by
  obtain ⟨i, hi⟩ := exists_a_of_order_eight e hx
  have hq : orderOf (e x) = 8 := by rw [MulEquiv.orderOf_eq]; exact hx
  have hHq : (zpowers (a 1 : QuaternionGroup 4)).carrier ⊇ {g | ∃ k : ZMod (2 * 4), g = a k} := by
    rintro _ ⟨k, rfl⟩
    refine ⟨(k.val : ℤ), ?_⟩
    simp only [zpow_natCast]
    rw [a_one_pow, ZMod.natCast_zmod_val]
  have hxmem : e x ∈ zpowers (a 1 : QuaternionGroup 4) := hHq ⟨i, hi⟩
  have hcard1 : Nat.card ↥(zpowers (a 1 : QuaternionGroup 4)) = 8 := by
    rw [Nat.card_zpowers, orderOf_a_one]
  have hcard2 : Nat.card ↥(zpowers (e x)) = 8 := by rw [Nat.card_zpowers, hq]
  have hle : zpowers (e x) ≤ zpowers (a 1 : QuaternionGroup 4) := (zpowers_le).2 hxmem
  have heq : zpowers (e x) = zpowers (a 1 : QuaternionGroup 4) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard1, hcard2])
  have hy' : e y * a i = a i * e y := by
    have := congrArg e hy
    rwa [map_mul, map_mul, hi] at this
  rcases hk : e y with k | k
  · have : e y ∈ zpowers (e x) := by rw [heq, hk]; exact hHq ⟨k, rfl⟩
    have h2 : e y ∈ (zpowers x).map e.toMonoidHom := by
      rw [MonoidHom.map_zpowers]; exact this
    obtain ⟨y', hy'mem, hy'eq⟩ := h2
    have : y' = y := e.injective hy'eq
    rwa [← this]
  · exfalso
    rw [hk] at hy'
    rw [xa_mul_a, a_mul_xa] at hy'
    have hxa := QuaternionGroup.xa.inj hy'
    have h2i : (2 : ZMod (2 * 4)) * i = 0 := by linear_combination hxa
    have hv : ∀ j : ZMod (2 * 4), (2 : ZMod (2 * 4)) * j = 0 → j = 0 ∨ j = 4 := by decide
    rcases hv i h2i with h0 | h4
    · rw [h0] at hi
      have : e x = 1 := by rw [hi]; rfl
      have := (map_eq_one_iff e e.injective).1 this
      rw [this, orderOf_one] at hx
      omega
    · rw [h4] at hi
      have h2 : orderOf (a (4 : ZMod (2 * 4)) : QuaternionGroup 4) = 2 := by
        rw [orderOf_a]; decide
      rw [← hi, MulEquiv.orderOf_eq, hx] at h2
      omega

theorem q16_exists_inv (e : X ≃* QuaternionGroup 4) {x : X} (hx : orderOf x = 8) :
    ∃ b : X, b * x * b⁻¹ = x⁻¹ ∧ b * b = x ^ 4 := by
  obtain ⟨i, hi⟩ := exists_a_of_order_eight e hx
  refine ⟨e.symm (xa 0), ?_, ?_⟩
  · apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hi, map_inv, hi]
    have := conj_xa_a 0 i
    rw [this]
    rfl
  · apply e.injective
    rw [map_mul, MulEquiv.apply_symm_apply, map_pow, hi, xa_mul_xa]
    have hq : orderOf (a i : QuaternionGroup 4) = 8 := by rw [← hi, MulEquiv.orderOf_eq]; exact hx
    rw [orderOf_a] at hq
    have hodd : ∀ j : ZMod (2 * 4), 2 * 4 / Nat.gcd (2 * 4) j.val = 8 → 4 * j = 4 := by decide
    have h4 := hodd i hq
    have e1 : (a i : QuaternionGroup 4) ^ 4 = a (4 * i) := by
      have := a_one_pow (n := 4) 4
      calc (a i : QuaternionGroup 4) ^ 4 = (a i) * (a i) * (a i) * (a i) := by
            simp only [pow_succ, pow_zero, one_mul]
        _ = a (i + i + i + i) := by simp only [a_mul_a]
        _ = a (4 * i) := by congr 1; ring
    rw [e1, h4]
    congr 1

theorem q16_card (e : X ≃* QuaternionGroup 4) : Nat.card X = 16 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem q16_exists_order_eight (e : X ≃* QuaternionGroup 4) : ∃ x : X, orderOf x = 8 := by
  refine ⟨e.symm (a 1), ?_⟩
  rw [MulEquiv.orderOf_eq, orderOf_a_one]

end Q16

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65
