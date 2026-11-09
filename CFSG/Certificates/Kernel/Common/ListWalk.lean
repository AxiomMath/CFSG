module

public import Init

public section

namespace CFSG.KC.ListWalk

@[expose] def walk {α β : Type} (P : α → β → Nat → Bool) : List α → List β → Nat → Bool
  | a :: as, b :: bs, c => P a b c && walk P as bs (c + 1)
  | _, _, _ => true

theorem walk_getD {α β : Type} (P : α → β → Nat → Bool) (d : α) (e : β) :
    ∀ (as : List α) (bs : List β) (c : Nat), walk P as bs c = true →
      ∀ i, i < as.length → i < bs.length → P (as.getD i d) (bs.getD i e) (c + i) = true := by
  intro as
  induction as with
  | nil => intro _ _ _ i hi; simp at hi
  | cons a as ih =>
    intro bs c h i hi hj
    cases bs with
    | nil => simp at hj
    | cons b bs =>
      simp only [walk, Bool.and_eq_true] at h
      cases i with
      | zero => simpa using h.1
      | succ k =>
        have := ih bs (c + 1) h.2 k (by simpa using hi) (by simpa using hj)
        simpa [Nat.add_assoc, Nat.add_comm 1 k] using this

theorem walkA_getD {α β : Type} (P : α → β → Nat → Bool) (d : α) (e : β) (A : Array α) (B : Array β)
    (h : walk P A.toList B.toList 0 = true) :
    ∀ i, i < A.size → i < B.size → P (A.getD i d) (B.getD i e) i = true := by
  intro i hi hj
  have := walk_getD P d e A.toList B.toList 0 h i (by simpa using hi) (by simpa using hj)
  simpa [Array.getD, hi, hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem] using this

end CFSG.KC.ListWalk

end
