module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Equiv

@[expose] def sym8C : Perm (Fin 8) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4

@[expose] def sym8U1 : Perm (Fin 8) := swap 5 6

@[expose] def sym8U2 : Perm (Fin 8) := swap 6 7

theorem sym8C_pow_five : sym8C ^ 5 = 1 := by
  unfold sym8C
  decide

theorem sym8C_ne_one : sym8C ≠ 1 := by
  unfold sym8C
  decide

theorem orderOf_sym8C : orderOf sym8C = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact orderOf_eq_prime sym8C_pow_five sym8C_ne_one

theorem sym8U1_mul_self : sym8U1 * sym8U1 = 1 := by
  unfold sym8U1
  decide

theorem sym8U2_mul_self : sym8U2 * sym8U2 = 1 := by
  unfold sym8U2
  decide

theorem sym8U1_comm_C : sym8U1 * sym8C = sym8C * sym8U1 := by
  unfold sym8U1 sym8C
  decide

theorem sym8U2_comm_C : sym8U2 * sym8C = sym8C * sym8U2 := by
  unfold sym8U2 sym8C
  decide

theorem sym8_cube : (sym8U1 * sym8U2) ^ 3 = 1 := by
  unfold sym8U1 sym8U2
  decide

theorem sym8_U1U2_ne_one : sym8U1 * sym8U2 ≠ 1 := by
  unfold sym8U1 sym8U2
  decide

end CFSG.EvenSporadicStandard.HSStd
