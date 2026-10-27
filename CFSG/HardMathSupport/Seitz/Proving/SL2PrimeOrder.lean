module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.HardMathSupport.Seitz.Proving

theorem card_SL2_field_eq (k : Type*) [Field k] [Fintype k] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) k) = (Fintype.card k ^ 2 - 1) * Fintype.card k := by
  rw [Matrix.card_SL_field, Fin.prod_univ_two]
  have hq : 2 ≤ Fintype.card k := by
    have := Fintype.one_lt_card (α := k)
    omega
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card k = m + 2 := ⟨Fintype.card k - 2, by omega⟩
  rw [hm]
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : (m + 2) ^ 2 - (m + 2) = (m + 2) * (m + 1) := Nat.sub_eq_of_eq_add (by ring)
  simp only [pow_zero, pow_one, Fin.val_zero, Fin.val_one, e1]
  apply Nat.div_eq_of_eq_mul_left (by omega)
  rw [e2]
  ring

theorem exists_orderOf_eq_prime_SL2 {k : Type*} [Field k] [Finite k] {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card k ^ 2 - 1) :
    ∃ x : Matrix.SpecialLinearGroup (Fin 2) k, orderOf x = p := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) k) =
      (Nat.card k ^ 2 - 1) * Nat.card k := by
    rw [card_SL2_field_eq k, Nat.card_eq_fintype_card (α := k)]
  have hdvdG : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) k) := by
    rw [hcard]
    exact Dvd.dvd.mul_right hdvd _
  exact exists_prime_orderOf_dvd_card' (G := Matrix.SpecialLinearGroup (Fin 2) k) p hdvdG

end CFSG.HardMathSupport.Seitz.Proving

end
