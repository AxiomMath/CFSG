module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.CGT.PushingUpLit.CGT6E

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1000 in
theorem gl23_two_element_central :
    ∀ u τ : GL (Fin 2) (ZMod 3), u ^ 3 = 1 → u ≠ 1 → τ * u = u * τ → τ ^ 16 = 1 →
      (τ = 1 ∨ τ = -1) := by
  decide +kernel

theorem natCard_gl23 : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Matrix.card_GL_field]
  simp [Finset.prod_fin_eq_prod_range, Finset.prod_range_succ]

theorem gl23_pow_sixteen {τ : GL (Fin 2) (ZMod 3)} {m : ℕ} (h : τ ^ 2 ^ m = 1) : τ ^ 16 = 1 := by
  have hord2 : orderOf τ ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one h
  have hord48 : orderOf τ ∣ 16 * 3 := by
    have := orderOf_dvd_natCard τ
    rw [natCard_gl23] at this
    simpa using this
  have hcop : Nat.Coprime (orderOf τ) 3 :=
    Nat.Coprime.coprime_dvd_left hord2 (Nat.Coprime.pow_left _ (by norm_num))
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right hord48)

end CFSG.CGT.PushingUpLit.CGT6E
