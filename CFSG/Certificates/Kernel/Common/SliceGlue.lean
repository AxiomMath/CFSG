module

public import Init

public section

namespace CFSG.KC.SliceGlue

@[expose] def slice {α : Type} (l : List α) (a b : Nat) : List α := (l.drop a).take b

theorem all_of_slices {α : Type} (p : α → Bool) (b m : Nat) (T : List α) (hT : T.length ≤ m * b)
    (h : ∀ j < m, (slice T (j * b) b).all p = true) : T.all p = true := by
  have key : ∀ j, j ≤ m → (T.take (j * b)).all p = true := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      rw [Nat.succ_mul, List.take_add, List.all_append, ih (by omega), Bool.true_and]
      exact h j (by omega)
  have := key m (Nat.le_refl m)
  rwa [List.take_of_length_le hT] at this

theorem sum_map_of_all_eq {α : Type} (f : α → Nat) (c : Nat) :
    ∀ (L : List α), (L.all fun a => f a == c) = true → (L.map f).sum = c * L.length
  | [], _ => by simp
  | a :: L, h => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    rw [List.map_cons, List.sum_cons, sum_map_of_all_eq f c L h.2, h.1, List.length_cons,
      Nat.mul_succ, Nat.add_comm]

theorem filter_eq_of_slices {α : Type} (p : α → Bool) (b : Nat) :
    ∀ (Rs : List (List α)) (l : List α), l.length ≤ Rs.length * b →
      (∀ j < Rs.length, (slice l (j * b) b).filter p = Rs.getD j []) → l.filter p = Rs.flatten
  | [], l, hl, _ => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst this; rfl
  | R :: Rs, l, hl, h => by
    have h0 := h 0 (by simp)
    simp only [slice, Nat.zero_mul, List.drop_zero, List.getD_cons_zero] at h0
    rw [← List.take_append_drop b l, List.filter_append, h0, List.flatten_cons]
    congr 1
    refine filter_eq_of_slices p b Rs (l.drop b) ?_ fun j hj => ?_
    · simp only [List.length_drop, List.length_cons] at hl ⊢
      rw [Nat.succ_mul] at hl
      omega
    · have := h (j + 1) (by simp; omega)
      simp only [slice, List.getD_cons_succ] at this ⊢
      rw [List.drop_drop, ← this]
      congr 3
      rw [Nat.succ_mul, Nat.add_comm]

theorem map_eq_of_getD {α β : Type} (f : α → β) (d : α) (e : β) :
    ∀ (L : List α) (R : List β), L.length = R.length →
      (∀ i < L.length, f (L.getD i d) = R.getD i e) → L.map f = R
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | x :: L, y :: R, hl, h => by
    rw [List.map_cons, map_eq_of_getD f d e L R (by simpa using hl) fun i hi =>
      h (i + 1) (by simp; omega)]
    have := h 0 (by simp)
    simp only [List.getD_cons_zero] at this
    rw [this]

end CFSG.KC.SliceGlue

end
