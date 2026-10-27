module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.NodeFamily

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Blueprint.Chevalley

section SmallCheck

variable (τ : Tag) (s : Fin τ.rank) (wTab uTab : List (List (Fin τ.rank)))

@[expose] def ClassSepSmall (A B : ℕ) : Prop :=
  ∀ n a b : ℕ, 3 ≤ n → n ≤ 5 → 0 < a → a < 2 ^ n - 1 → b < n → a.testBit b = true → a ≠ 2 ^ b →
    ∀ p q : Fin A × Fin B,
      (∀ i : Fin τ.rank, (((2 ^ n - 1 : ℕ) : ℤ)) ∣
        (((a : ℤ) • famX τ s (fun i : Fin A => wTab.getD i []) (fun j : Fin B => uTab.getD j [])
            p.1 p.2 - (2 : ℤ) ^ b • famB τ s (fun i : Fin A => wTab.getD i []) p.1) i -
         ((a : ℤ) • famX τ s (fun i : Fin A => wTab.getD i []) (fun j : Fin B => uTab.getD j [])
            q.1 q.2 - (2 : ℤ) ^ b • famB τ s (fun i : Fin A => wTab.getD i []) q.1) i)) → p = q

end SmallCheck

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
