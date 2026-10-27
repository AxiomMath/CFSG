module

public import Certificates.Data.Kernel.GilmanCensus.Fast2

public section

namespace Certificates.GilmanCensusK

theorem mapR_eq {α β : Type} (f : α → β) (l : List α) : mapR f l = l.map f := by
  induction l with
  | nil => rfl
  | cons a t ih => exact congrArg (f a :: ·) ih

theorem anyR_eq {α : Type} (p : α → Bool) (l : List α) : anyR p l = l.any p := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    change Bool.rec (motive := fun _ => Bool) (anyR p t) true (p a) = _
    rw [ih, List.any_cons]
    cases p a <;> simp

theorem allR_eq {α : Type} (p : α → Bool) (l : List α) : allR p l = l.all p := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    change Bool.rec (motive := fun _ => Bool) false (allR p t) (p a) = _
    rw [ih, List.all_cons]
    cases p a <;> simp

theorem lenR_eq {α : Type} (l : List α) : lenR l = l.length := by
  induction l with
  | nil => rfl
  | cons a t ih => exact congrArg (· + 1) ih

theorem getDR_eq {α : Type} (l : List α) (i : Nat) (d : α) : getDR l i d = l.getD i d := by
  induction l generalizing i with
  | nil => rfl
  | cons a t ih =>
    cases i with
    | zero => rfl
    | succ j => exact ih j

theorem zipWithR_eq {α β γ : Type} (f : α → β → γ) (l₁ : List α) (l₂ : List β) :
    zipWithR f l₁ l₂ = List.zipWith f l₁ l₂ := by
  induction l₁ generalizing l₂ with
  | nil => rfl
  | cons a t ih =>
    cases l₂ with
    | nil => rfl
    | cons b u => exact congrArg (f a b :: ·) (ih u)

theorem rangeFromR_eq (k i : Nat) : rangeFromR k i = List.range' i k := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih => exact congrArg (i :: ·) (ih (i + 1))

theorem rangeR_eq (k : Nat) : rangeR k = List.range k := by
  rw [rangeR, rangeFromR_eq, List.range_eq_range']

theorem natBeq_eq (a b : Nat) : Nat.beq a b = (a == b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq]
  constructor
  · exact Nat.eq_of_beq_eq_true
  · intro h
    subst h
    exact Nat.beq_refl _

theorem dotR_eq (v w : List Nat) : dotR v w = dotS v w := by
  induction v generalizing w with
  | nil => rfl
  | cons a t ih =>
    cases w with
    | nil => rfl
    | cons b u =>
      change a * b + dotR t u = _
      rw [ih u, dotS]

theorem dot3R_eq (v w : List Nat) : dot3R v w = dot3K v w := by
  rw [dot3R, dotR_eq]
  rfl

theorem toIR_eq (rs : List (List Nat)) : toIR rs = toI rs := by
  have hm : mapR Int.ofNat = fun r : List Nat => r.map Int.ofNat := by
    funext r
    exact mapR_eq _ r
  rw [toIR, mapR_eq, hm]
  rfl

end Certificates.GilmanCensusK

end
