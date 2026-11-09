module

public import Certificates.Data.Kernel.Lnth
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KS.ListSlices

open CFSG.KC

theorem lnth_nil {α : Type} (d : α) (j : Nat) : lnth d [] j = d := rfl

theorem lnth_cons_zero {α : Type} (d a : α) (l : List α) : lnth d (a :: l) 0 = a := rfl

theorem lnth_cons_succ {α : Type} (d a : α) (l : List α) (j : Nat) :
    lnth d (a :: l) (j + 1) = lnth d l j := rfl

theorem filter_slices (p : Nat → Bool) (L : Nat) (R : List (List Nat)) :
    ∀ k, (∀ s < k, ((List.range' (L * s) L).filter p == lnth [] R s) = true) →
      (List.range' 0 (L * k)).filter p = ((List.range k).map (lnth [] R)).flatten
  | 0, _ => by simp
  | k + 1, h => by
    have hk := beq_iff_eq.mp (h k (by omega))
    rw [Nat.mul_succ, ← List.range'_append_1, List.filter_append,
      filter_slices p L R k (fun s hs => h s (by omega)), Nat.zero_add, hk, List.range_succ,
      List.map_append, List.flatten_append]
    simp

theorem all_flatten {α : Type} (f : α → Bool) : ∀ (G : List (List α)),
    (∀ g < G.length, (lnth [] G g).all f = true) → G.flatten.all f = true
  | [], _ => rfl
  | a :: G, h => by
    rw [List.flatten_cons, List.all_append, Bool.and_eq_true]
    refine ⟨h 0 (by simp), all_flatten f G fun g hg => ?_⟩
    have := h (g + 1) (by simp; omega)
    rwa [lnth_cons_succ] at this

theorem flatMap_pairs_eq (F : Nat → List Nat) : ∀ (E : List (Nat × List Nat)),
    (∀ e ∈ E, F e.1 = e.2) →
      (E.map Prod.fst).flatMap (fun i => (F i).map fun j => (i, j)) =
        E.flatMap fun e => e.2.map fun j => (e.1, j)
  | [], _ => rfl
  | e :: E, h => by
    rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, h e (by simp),
      flatMap_pairs_eq F E fun e' he' => h e' (by simp [he'])]

theorem all_chunks {α : Type} (f : α → Bool) (m : Nat) : ∀ (n : Nat) (l : List α),
    l.length ≤ m * n → (∀ s < n, ((l.drop (m * s)).take m).all f = true) → l.all f = true
  | 0, l, hl, _ => by
    rw [Nat.mul_zero] at hl
    rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)]
    rfl
  | n + 1, l, hl, h => by
    rw [← List.take_append_drop m l, List.all_append, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by omega), all_chunks f m n (l.drop m) ?_ fun s hs => ?_⟩
    · rw [List.length_drop]
      rw [Nat.mul_add, Nat.mul_one] at hl
      exact Nat.sub_le_iff_le_add.mpr hl
    · have := h (s + 1) (by omega)
      have e : m * (s + 1) = m + m * s := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      rw [List.drop_drop]
      rw [e] at this
      exact this

end CFSG.KS.ListSlices
