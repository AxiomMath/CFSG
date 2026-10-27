module

public import Certificates.Data.Kernel.MonsterB.Co2Mem

public section

namespace CFSG.KC.Co2Mem

open CFSG.KC.Enum CFSG.KS

theorem memK_succ (n w F y : Nat) :
    memK (n + 1) w F y = (Nat.beq (pg w (mask w) F n) y || memK n w F y) := by
  change Bool.rec (motive := fun _ => Bool) (memK n w F y) true (Nat.beq (pg w (mask w) F n) y) = _
  cases Nat.beq (pg w (mask w) F n) y <;> rfl

theorem memK_iff (n w F y : Nat) : memK n w F y = true ↔ ∃ t < n, pg w (mask w) F t = y := by
  induction n with
  | zero =>
    change false = true ↔ _
    simp
  | succ n ih =>
    rw [memK_succ, Bool.or_eq_true, ih, Nat.beq_eq]
    constructor
    · rintro (h | ⟨t, ht, h⟩)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨t, Nat.lt_succ_of_lt ht, h⟩
    · rintro ⟨t, ht, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
      · exact Or.inr ⟨t, ht, h⟩
      · exact Or.inl h

end CFSG.KC.Co2Mem

end
