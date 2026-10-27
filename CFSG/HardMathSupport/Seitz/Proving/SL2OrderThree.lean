module

public import CFSG.HardMathSupport.Seitz.Proving.SL2PrimeOrder

public section

namespace CFSG.HardMathSupport.Seitz.Proving

theorem exists_orderOf_three_SL2 (k : Type) [Field k] [Finite k]
    (h3 : 3 ∣ Nat.card k ^ 2 - 1) :
    ∃ x : Matrix.SpecialLinearGroup (Fin 2) k, orderOf x = 3 :=
  exists_orderOf_eq_prime_SL2 Nat.prime_three h3

end CFSG.HardMathSupport.Seitz.Proving

end
