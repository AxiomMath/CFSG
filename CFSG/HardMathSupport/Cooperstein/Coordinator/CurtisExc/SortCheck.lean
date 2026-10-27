module

public import Aesop.BuiltinRules
public import Batteries.Data.List.Lemmas
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.ToDual

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

@[expose] def mergeN : ℕ → List ℕ → List ℕ → List ℕ
  | 0, a, b => a ++ b
  | _ + 1, [], b => b
  | _ + 1, a :: as, [] => a :: as
  | f + 1, x :: xs, y :: ys =>
    if x ≤ y then x :: mergeN f xs (y :: ys) else y :: mergeN f (x :: xs) ys

theorem mergeN_perm : ∀ (f : ℕ) (a b : List ℕ), (mergeN f a b).Perm (a ++ b)
  | 0, a, b => List.Perm.refl _
  | f + 1, [], b => by simp [mergeN]
  | f + 1, a :: as, [] => by simp [mergeN]
  | f + 1, x :: xs, y :: ys => by
    unfold mergeN
    split_ifs
    · exact (mergeN_perm f xs (y :: ys)).cons x
    · refine ((mergeN_perm f (x :: xs) ys).cons y).trans ?_
      simpa using (List.perm_middle (a := y) (l₁ := x :: xs) (l₂ := ys)).symm

@[expose] def mergePairs : List (List ℕ) → List (List ℕ)
  | a :: b :: t => mergeN (a.length + b.length) a b :: mergePairs t
  | l => l

theorem mergePairs_perm : ∀ l : List (List ℕ), (mergePairs l).flatten.Perm l.flatten
  | [] => List.Perm.refl _
  | [a] => List.Perm.refl _
  | a :: b :: t => by
    unfold mergePairs
    simp only [List.flatten_cons]
    exact (((mergeN_perm _ a b).append (mergePairs_perm t)).trans (by simp [List.append_assoc]))

@[expose] def msortLoop : ℕ → List (List ℕ) → List (List ℕ)
  | 0, l => l
  | f + 1, l => msortLoop f (mergePairs l)

theorem msortLoop_perm : ∀ (f : ℕ) (l : List (List ℕ)), (msortLoop f l).flatten.Perm l.flatten
  | 0, _ => List.Perm.refl _
  | f + 1, l => (msortLoop_perm f (mergePairs l)).trans (mergePairs_perm l)

@[expose] def msortN (l : List ℕ) : List ℕ := (msortLoop 9 (l.map fun x => [x])).flatten

theorem msortN_perm (l : List ℕ) : (msortN l).Perm l := by
  refine (msortLoop_perm 9 _).trans ?_
  induction l with
  | nil => exact List.Perm.refl _
  | cons a t ih => simpa using ih.cons a

@[expose] def strictB : List Nat → Bool
  | a :: b :: t => decide (a < b) && strictB (b :: t)
  | _ => true

theorem pairwise_of_strictB : ∀ l : List ℕ, strictB l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [a], _ => by simp
  | a :: b :: t, h => by
    simp only [strictB, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pairwise_of_strictB (b :: t) h.2
    refine List.pairwise_cons.2 ⟨fun x hx => ?_, ih⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 ((List.pairwise_cons.1 ih).1 x hx)

theorem nodup_of_strictB {l : List ℕ} (h : strictB (msortN l) = true) : l.Nodup :=
  (msortN_perm l).nodup_iff.1 ((pairwise_of_strictB _ h).imp Nat.ne_of_lt)

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
