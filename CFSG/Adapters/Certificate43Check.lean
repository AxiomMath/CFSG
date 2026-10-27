module

public import Mathlib.Algebra.Group.End
import Mathlib.Data.Fintype.Perm

public section

namespace CFSG.Adapters

theorem certificate43_holds :
      ∀ s t : Equiv.Perm (Fin 3),
        (s ≠ 1 ∧ s ^ 2 = 1) → (t ≠ 1 ∧ t ^ 2 = 1) → s ≠ t →
          (s * t) ^ 3 = 1 ∧ s * t ≠ 1 := by
  let : DecidableEq (Equiv.Perm (Fin 3)) := Fintype.decidableEqEquivFintype
  exact by decide

end CFSG.Adapters
