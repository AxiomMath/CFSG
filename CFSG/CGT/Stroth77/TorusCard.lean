module

public import CFSG.CGT.Stroth77.TypePredicates

public section

namespace CFSG.CGT.Stroth77

theorem card_torus (k : Fin 3 → ℕ) :
    Nat.card (Torus k) = 2 ^ (k 0 + k 1 + k 2) :=
  natCard_torus k

theorem card_torus_t100 (m : ℕ) :
    Nat.card (Torus (Type100.k m)) = 2 ^ (3 * m + 2) := by
  rw [card_torus]
  congr 1
  simp [Type100.k]
  ring

@[simp] theorem three_mul_succ_add_two (m : ℕ) : 3 * (m + 1) + 2 = 3 * m + 5 := by ring

@[simp] theorem three_mul_add_two_add_two (t : ℕ) : 3 * (t + 2) + 2 = 3 * t + 8 := by ring

@[simp] theorem three_mul_add_two_add_four (s : ℕ) : 3 * (s + 2) + 4 = 3 * s + 10 := by ring

end CFSG.CGT.Stroth77
