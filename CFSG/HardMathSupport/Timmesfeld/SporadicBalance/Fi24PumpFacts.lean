module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24ThreeClasses
public import CFSG.Sporadic.Fi24.ExtClass

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three

open CFSG.Sporadic.Fi24 (J cls)

@[expose] def FiveFix (g : J) : Prop :=
  Nat.card {k : Fin 306936 // g • k = k} = 36 ∧
    (∀ d : Fin 306936, g • d = d →
      Nat.card {k : Fin 306936 // g • k = k ∧ k ≠ d ∧ cls k * cls d = cls d * cls k} = 21) ∧
    ∀ t : J, t * g = g * t → t ^ 3 = 1 →
      Nat.card {k : Fin 306936 // g • k = k ∧ t • k = k} % 5 ≠ 2

@[expose] def ThreePair (x : J) (p n : ℕ) : Prop :=
  ∃ v : J, orderOf v = p ∧ x * v = v * x ∧ Nat.card {k : Fin 306936 // v • k = k} = n

@[expose] def Fi24PumpFacts : Prop :=
  (∃ e f : J, e ^ 5 = 1 ∧ e ≠ 1 ∧ f ^ 5 = 1 ∧ e * f = f * e ∧ (∀ k < 5, f ≠ e ^ k) ∧
      ∀ a < 5, ∀ b < 5, a + b ≠ 0 → FiveFix (e ^ a * f ^ b)) ∧
    ThreePair (fi24Rep3 0) 13 6 ∧ ThreePair (fi24Rep3 1) 11 3 ∧ ThreePair (fi24Rep3 2) 7 0 ∧
    ThreePair (fi24Rep3 4) 13 6 ∧ Nat.card {k : Fin 306936 // fi24Rep3 3 • k = k} = 162

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three

end
