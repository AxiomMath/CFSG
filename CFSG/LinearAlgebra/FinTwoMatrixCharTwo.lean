module

public import CFSG.Quasithin.Background.A1cA130

public section

namespace CFSG.LinearAlgebra

theorem fin_two_sq_eq_one_of_pow_two_pow_eq_one {F : Type*} [CommRing F] [IsDomain F]
    [CharP F 2] {M : Matrix (Fin 2) (Fin 2) F} {k : ℕ} (hM : M ^ 2 ^ k = 1) : M ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (M - 1) ^ 2 ^ k = 0 := by
    rw [sub_pow_char_pow_of_commute 2 k (Commute.one_right M), hM, one_pow, sub_self]
  have hN2 : (M - 1) ^ 2 = 0 :=
    CFSG.Quasithin.A1c.sq_eq_zero_of_pow_eq_zero_fin_two (pow_pos (by norm_num) k) hN
  have hM' : M = (M - 1) + 1 := by abel
  rw [hM', add_pow_char_of_commute 2 (Commute.one_right (M - 1)), hN2, one_pow]
  simp

end CFSG.LinearAlgebra
