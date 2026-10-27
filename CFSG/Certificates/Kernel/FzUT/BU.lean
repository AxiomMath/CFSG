module

public import Certificates.Data.Kernel.FzUT.BU
public import Mathlib.Data.Finset.Card

public section

namespace CFSG.KC.FzUT

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem impB_eq (a b : Bool) : impB a b = (!a || b) := by cases a <;> rfl

theorem andB_true {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  rw [andB_eq, Bool.and_eq_true]

theorem orB_true {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  rw [orB_eq, Bool.or_eq_true]

theorem impB_true {a b : Bool} : impB a b = true ↔ (a = true → b = true) := by
  cases a <;> simp [impB_eq]

theorem allB_succ (n : Nat) (p : Nat → Bool) : allB (n + 1) p = andB (p n) (allB n p) := rfl

theorem cntB_succ (n : Nat) (p : Nat → Bool) :
    cntB (n + 1) p = cntB n p + (if p n = true then 1 else 0) := by
  show Bool.rec (motive := fun _ => Nat) (cntB n p) (Nat.succ (cntB n p)) (p n) = _
  cases p n <;> rfl

theorem allB_iff (n : Nat) (p : Nat → Bool) : allB n p = true ↔ ∀ i < n, p i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    rw [allB_succ, andB_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · exact h2 i h
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem cntB_eq (n : Nat) (p : Nat → Bool) :
    cntB n p = ((Finset.range n).filter (fun i => p i = true)).card := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cntB_succ, ih, Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]
    · rfl

theorem allL_iff (l : List Nat) (p : Nat → Bool) : allL l p = true ↔ ∀ x ∈ l, p x = true := by
  induction l with
  | nil => exact ⟨fun _ x hx => absurd hx (List.not_mem_nil), fun _ => rfl⟩
  | cons a l ih =>
    change andB (p a) (allL l p) = true ↔ _
    rw [andB_true, ih]
    simp

theorem anyL_iff (l : List Nat) (p : Nat → Bool) : anyL l p = true ↔ ∃ x ∈ l, p x = true := by
  induction l with
  | nil =>
    exact ⟨fun h => absurd (h : false = true) Bool.false_ne_true,
      fun ⟨x, hx, _⟩ => absurd hx List.not_mem_nil⟩
  | cons a l ih =>
    change orB (p a) (anyL l p) = true ↔ _
    rw [orB_true, ih]
    simp

end CFSG.KC.FzUT
