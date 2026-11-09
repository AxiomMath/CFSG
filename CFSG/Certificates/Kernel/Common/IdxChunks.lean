module

public import Init

public section

namespace CFSG.KC.IdxChunks

theorem idx_append {α : Type _} (f : Nat → List α → Bool) (g : Nat → α → Bool)
    (h0 : ∀ n, f n [] = true) (hc : ∀ n a l, f n (a :: l) = (g n a && f (n + 1) l)) :
    ∀ (l₁ l₂ : List α) (n : Nat), f n (l₁ ++ l₂) = (f n l₁ && f (n + l₁.length) l₂)
  | [], l₂, n => by rw [List.nil_append, h0, Bool.true_and, List.length_nil, Nat.add_zero]
  | a :: l₁, l₂, n => by
    rw [List.cons_append, hc, hc, idx_append f g h0 hc l₁ l₂ (n + 1), Bool.and_assoc,
      List.length_cons, Nat.add_assoc, Nat.add_comm 1]

theorem idx_chunks_of {α : Type _} (f : Nat → List α → Bool) (g : Nat → α → Bool)
    (h0 : ∀ n, f n [] = true) (hc : ∀ n a l, f n (a :: l) = (g n a && f (n + 1) l)) (c : Nat) :
    ∀ (m : Nat) (L : List α) (n : Nat), L.length ≤ m * c →
      (∀ j < m, f (n + j * c) ((L.drop (j * c)).take c) = true) → f n L = true
  | 0, L, n, hl, _ => by
    rw [Nat.zero_mul] at hl
    rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)]
    exact h0 n
  | m + 1, L, n, hl, h => by
    rw [← List.take_append_drop c L, idx_append f g h0 hc, Bool.and_eq_true]
    constructor
    · have := h 0 (Nat.succ_pos m)
      rwa [Nat.zero_mul, Nat.add_zero, List.drop_zero] at this
    · by_cases hcl : c ≤ L.length
      · rw [List.length_take, Nat.min_eq_left hcl]
        refine idx_chunks_of f g h0 hc c m (L.drop c) (n + c) ?_ fun j hj => ?_
        · rw [List.length_drop]
          rw [Nat.succ_mul] at hl
          omega
        · have := h (j + 1) (by omega)
          rw [List.drop_drop, Nat.add_assoc, Nat.add_comm c (j * c)]
          rwa [Nat.succ_mul] at this
      · rw [List.drop_eq_nil_of_le (by omega)]
        exact h0 _

theorem all_chunks_of {α : Type _} (p : α → Bool) (c : Nat) :
    ∀ (m : Nat) (L : List α), L.length ≤ m * c →
      (∀ j < m, ((L.drop (j * c)).take c).all p = true) → L.all p = true := by
  intro m L hl h
  have := idx_chunks_of (fun _ l => l.all p) (fun _ a => p a) (fun _ => rfl)
    (fun _ _ _ => rfl) c m L 0 hl (fun j hj => h j hj)
  exact this

theorem length_filter_chunks {α : Type _} (p : α → Bool) (c : Nat) :
    ∀ (m : Nat) (L : List α), L.length ≤ m * c →
      (L.filter p).length = ((List.range m).map fun j => (((L.drop (j * c)).take c).filter p).length).sum
  | 0, L, hl => by
    rw [Nat.zero_mul] at hl
    rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)]
    rfl
  | m + 1, L, hl => by
    rw [← List.take_append_drop c L]
    rw [List.take_append_drop]
    have e : L = L.take c ++ L.drop c := (List.take_append_drop c L).symm
    rw [congrArg (fun l => (List.filter p l).length) e]
    rw [List.filter_append, List.length_append, List.range_succ_eq_map, List.map_cons,
      List.sum_cons, Nat.zero_mul, List.drop_zero, List.map_map]
    congr 1
    rw [length_filter_chunks p c m (L.drop c) (by rw [List.length_drop, Nat.succ_mul] at *; omega)]
    congr 1
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp, List.drop_drop, Nat.succ_mul, Nat.add_comm (j * c) c]

theorem chain_of {α : Type _} (F : List α → Nat → Nat) (hnil : ∀ a, F [] a = a)
    (happ : ∀ l₁ l₂ a, F (l₁ ++ l₂) a = F l₂ (F l₁ a)) (c : Nat) :
    ∀ (m : Nat) (T : List α) (R : Nat → Nat), T.length ≤ m * c →
      (∀ j < m, F ((T.drop (j * c)).take c) (R j) = R (j + 1)) → F T (R 0) = R m
  | 0, T, R, hl, _ => by
    rw [Nat.zero_mul] at hl
    rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl), hnil]
  | m + 1, T, R, hl, h => by
    rw [← List.take_append_drop c T, happ]
    have h0 := h 0 (Nat.succ_pos m)
    rw [Nat.zero_mul, List.drop_zero] at h0
    rw [h0]
    refine chain_of F hnil happ c m (T.drop c) (fun j => R (j + 1)) ?_ fun j hj => ?_
    · rw [List.length_drop, Nat.succ_mul] at *; omega
    · have := h (j + 1) (by omega)
      rw [List.drop_drop, Nat.add_comm c (j * c)]
      rwa [Nat.succ_mul] at this

end CFSG.KC.IdxChunks

end
