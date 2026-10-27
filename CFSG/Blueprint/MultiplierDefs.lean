module

public import CFSG.Assembly.LowTwoRankDefs

public noncomputable section

namespace CFSG.Blueprint.Multiplier

open Assembly.LowTwoRank

@[expose] def genericOrders (t : StatedLieTag) (n p f : ℕ) : ℕ × ℕ := by
  classical
  let q := p ^ f
  exact match t with
  | .PSL => (Nat.gcd n (q - 1), 1)
  | .PSU => (Nat.gcd n (q + 1), 1)
  | .PSp => (Nat.gcd 2 (q - 1), 1)
  | .POmegaOdd => (2, 1)
  | .POmegaPlus => if Even q then (1, 1) else
      if Even n then (2, 2) else (Nat.gcd 4 (q ^ n - 1), 1)
  | .POmegaMinus => (Nat.gcd 4 (q ^ n + 1), 1)
  | .E6 => (Nat.gcd 3 (q - 1), 1)
  | .twistedE6 => (Nat.gcd 3 (q + 1), 1)
  | .E7 => (Nat.gcd 2 (q - 1), 1)
  | _ => (1, 1)

abbrev generic (t : StatedLieTag) (n p f : ℕ) : Type :=
  Multiplicative (ZMod (genericOrders t n p f).1) ×
    Multiplicative (ZMod (genericOrders t n p f).2)

@[expose] def exceptionalOrders (t : StatedLieTag) (n p f : ℕ) : ℕ × ℕ :=
  match t, n, p, f with
  | .PSL, 2, 2, 2 | .PSL, 3, 2, 1 | .PSL, 4, 2, 1 | .PSU, 4, 2, 1
  | .PSp, 3, 2, 1 | .G2, 0, 2, 2 | .F4, 0, 2, 1 => (2, 1)
  | .PSL, 2, 3, 2 | .POmegaOdd, 3, 3, 1 | .G2, 0, 3, 1 => (3, 1)
  | .POmegaPlus, 4, 2, 1 | .PSU, 6, 2, 1 | .twistedB2, 0, 2, 3
  | .twistedE6, 0, 2, 1 => (2, 2)
  | .PSL, 3, 2, 2 => (4, 4)
  | .PSU, 4, 3, 1 => (3, 3)
  | _, _, _, _ => (1, 1)

abbrev exceptional (t : StatedLieTag) (n p f : ℕ) : Type :=
  Multiplicative (ZMod (exceptionalOrders t n p f).1) ×
    Multiplicative (ZMod (exceptionalOrders t n p f).2)

end CFSG.Blueprint.Multiplier
