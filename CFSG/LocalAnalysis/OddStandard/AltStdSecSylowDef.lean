module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.AltStdSec

@[expose] def OddRootCount (n : ℕ) : Prop :=
  ∀ P : Subgroup (Equiv.Perm (Fin n)), IsPGroup 2 P →
    (∀ P' : Subgroup (Equiv.Perm (Fin n)), IsPGroup 2 P' → P ≤ P' → P' = P) →
    ∀ y : Equiv.Perm (Fin n), y ∈ P → (∀ s ∈ P, s * y = y * s) → Equiv.Perm.sign y = 1 →
      y ≠ 1 → y * y = 1 →
      Nat.card {s : P // Equiv.Perm.sign (s : Equiv.Perm (Fin n)) = -1 ∧
        (s : Equiv.Perm (Fin n)) ^ 2 = y} <
        Nat.card {s : P // Equiv.Perm.sign (s : Equiv.Perm (Fin n)) = -1 ∧
          (s : Equiv.Perm (Fin n)) ^ 2 = 1}

end CFSG.OddStandard.AltStdSec
