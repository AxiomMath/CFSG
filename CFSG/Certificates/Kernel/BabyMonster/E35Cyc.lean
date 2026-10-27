module

public import Mathlib.Algebra.Group.Monoid

public section

namespace CFSG.KC.BM.E35

@[expose] def CycFacts {M : Type*} [Monoid M] (x g : M) : Prop :=
  x ^ 3 = 1 ∧ g ^ 10 = 1 ∧ g ^ 5 ≠ 1 ∧ g ^ 5 * x = x * g ^ 5 ∧
    x * (g ^ 9 * x * g) = g ^ 9 * x * g * x ∧
    x * (g ^ 9 * (g ^ 9 * x * g) * g) = g ^ 9 * (g ^ 9 * x * g) * g * x ∧
    g ^ 9 * x * g ≠ x ∧ (x * g ^ 9) ^ 4 * x * g ^ 4 ≠ 1

end CFSG.KC.BM.E35

end
