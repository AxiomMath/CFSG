module

public import Certificates.Data.CFSGNative.Fischer.Hyperoval

public section

namespace CFSG.KC.Misc.Lines

open CFSG.Fischer.Native

theorem forIn_ite_yield {α β : Type} (l : List α) (init : β) (c : α → Bool) (f : α → β → β) :
    forIn (m := Id) l init (fun a b =>
      if c a = true then pure (ForInStep.yield (f a b)) else pure (ForInStep.yield b)) =
    l.foldl (fun b a => if c a = true then f a b else b) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a t ih =>
    rw [List.forIn_cons]
    by_cases hc : c a = true
    · simp [hc, ih]
    · simp [hc, ih]

theorem forIn_cond_push {β : Type} (l : List Nat) (init : Array β) (p q : Nat → Bool)
    (g : Nat → β) :
    forIn (m := Id) l init (fun y s =>
      if p y = true then
        (if q y = true then pure (ForInStep.yield (s.push (g y))) else pure (ForInStep.yield s))
      else pure (ForInStep.yield s)) =
    init ++ ((l.filter fun y => p y && q y).map g).toArray := by
  induction l generalizing init with
  | nil => rfl
  | cons a t ih =>
    rw [List.forIn_cons]
    by_cases hp : p a = true
    · by_cases hq : q a = true
      · simp [hp, hq, ih]
      · simp [hp, hq, ih]
    · simp [hp, ih]

theorem id_bind_eq {α β : Type} (e : α) (k : α → Id β) : (bind (m := Id) e k) = k e := rfl

theorem legacyRange_size (n : Nat) : [:n].size = n := by
  simp [Std.Legacy.Range.size]

@[expose] def idxB (L : Array (Array Nat)) (i a : Nat) (r : Array Nat) (b : Nat) : Array Nat :=
  if (a != b) = true then r.set! ((L[i]!)[a]! * 693 + (L[i]!)[b]!) i else r

@[expose] def idxA (L : Array (Array Nat)) (i : Nat) (r : Array Nat) (a : Nat) : Array Nat :=
  (List.range 5).foldl (idxB L i a) r

@[expose] def idxI (L : Array (Array Nat)) (r : Array Nat) (i : Nat) : Array Nat :=
  (List.range 5).foldl (idxA L i) r

theorem lineIdx_eq (L : Array (Array Nat)) :
    lineIdx L = (List.range L.size).foldl (idxI L) (Array.replicate (693 * 693) L.size) := by
  unfold lineIdx
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [forIn_ite_yield, id_bind_eq, List.forIn_pure_yield_eq_foldl, legacyRange_size,
    List.range_eq_range']
  rfl

section Folds

variable {α : Type} (f : Array Nat → α → Array Nat) (H : α → Nat → Prop)
  [∀ x k, Decidable (H x k)] (V : α → Nat)
  (hf : ∀ (r : Array Nat) (x : α), (f r x).size = r.size ∧
    ∀ k < r.size, (f r x)[k]! = if H x k then V x else r[k]!)

include hf

theorem foldl_steps_size : ∀ (l : List α) (r : Array Nat), (l.foldl f r).size = r.size := by
  intro l
  induction l with
  | nil => intro r; rfl
  | cons x t ih => intro r; rw [List.foldl_cons, ih, (hf r x).1]

theorem foldl_steps_nohit : ∀ (l : List α) (r : Array Nat) (k : Nat), k < r.size →
    (∀ x ∈ l, ¬ H x k) → (l.foldl f r)[k]! = r[k]! := by
  intro l
  induction l with
  | nil => intro r k _ _; rfl
  | cons x t ih =>
    intro r k hk hno
    rw [List.foldl_cons, ih (f r x) k (by rw [(hf r x).1]; exact hk)
      (fun y hy => hno y (List.mem_cons_of_mem _ hy)), (hf r x).2 k hk,
      if_neg (hno x List.mem_cons_self)]

theorem foldl_steps_unique : ∀ (l : List α) (r : Array Nat) (k : Nat) (x0 : α), k < r.size →
    l.Nodup → x0 ∈ l → H x0 k → (∀ x ∈ l, H x k → x = x0) → (l.foldl f r)[k]! = V x0 := by
  intro l
  induction l with
  | nil => intro r k x0 _ _ h; exact absurd h (by simp)
  | cons x t ih =>
    intro r k x0 hk hnd hx0 hH huniq
    rw [List.foldl_cons]
    by_cases hx : x = x0
    · subst hx
      have hnot : ∀ y ∈ t, ¬ H y k := fun y hy hHy => by
        have := huniq y (List.mem_cons_of_mem _ hy) hHy
        subst this
        exact (List.nodup_cons.1 hnd).1 hy
      rw [foldl_steps_nohit f H V hf t (f r x) k (by rw [(hf r x).1]; exact hk) hnot,
        (hf r x).2 k hk, if_pos hH]
    · have hx0t : x0 ∈ t := by
        rcases List.mem_cons.1 hx0 with h | h
        · exact absurd h.symm hx
        · exact h
      exact ih (f r x) k x0 (by rw [(hf r x).1]; exact hk) (List.nodup_cons.1 hnd).2 hx0t hH
        (fun y hy hHy => huniq y (List.mem_cons_of_mem _ hy) hHy)

end Folds

section FoldsConst

variable {α : Type} (f : Array Nat → α → Array Nat) (H : α → Nat → Prop)
  [∀ x k, Decidable (H x k)] (v : Nat)
  (hf : ∀ (r : Array Nat) (x : α), (f r x).size = r.size ∧
    ∀ k < r.size, (f r x)[k]! = if H x k then v else r[k]!)

include hf

theorem foldl_steps_const : ∀ (l : List α) (r : Array Nat) (k : Nat), k < r.size →
    (l.foldl f r)[k]! = if ∃ x ∈ l, H x k then v else r[k]! := by
  intro l
  induction l with
  | nil => intro r k _; simp
  | cons x t ih =>
    intro r k hk
    rw [List.foldl_cons, ih (f r x) k (by rw [(hf r x).1]; exact hk), (hf r x).2 k hk]
    by_cases hx : H x k
    · simp [hx]
    · by_cases ht : ∃ y ∈ t, H y k
      · simp [hx, ht]
      · have : ¬ ∃ y ∈ x :: t, H y k := by
          rintro ⟨y, hy, hHy⟩
          rcases List.mem_cons.1 hy with rfl | hy
          · exact hx hHy
          · exact ht ⟨y, hy, hHy⟩
        simp [hx, ht]

end FoldsConst

@[expose] def Hit (L : Array (Array Nat)) (j k : Nat) : Prop :=
  ∃ a < 5, ∃ b < 5, a ≠ b ∧ (L[j]!)[a]! * 693 + (L[j]!)[b]! = k

instance (L : Array (Array Nat)) (j k : Nat) : Decidable (Hit L j k) := by
  unfold Hit
  infer_instance

theorem idxB_spec (L : Array (Array Nat)) (i a : Nat) (r : Array Nat) (b : Nat) :
    (idxB L i a r b).size = r.size ∧ ∀ k < r.size, (idxB L i a r b)[k]! =
      if ((a != b) = true ∧ (L[i]!)[a]! * 693 + (L[i]!)[b]! = k) then i else r[k]! := by
  unfold idxB
  by_cases hab : (a != b) = true
  · simp only [hab, if_true, true_and]
    refine ⟨Array.size_set! _ _ _, fun k hk => ?_⟩
    by_cases hkey : (L[i]!)[a]! * 693 + (L[i]!)[b]! = k
    · rw [if_pos hkey, hkey, Array.getElem!_set!_self _ _ _ hk]
    · rw [if_neg hkey, Array.getElem!_set!_ne _ _ _ _ hkey]
  · simp only [hab]
    exact ⟨rfl, fun k hk => rfl⟩

theorem idxA_spec (L : Array (Array Nat)) (i : Nat) (r : Array Nat) (a : Nat) :
    (idxA L i r a).size = r.size ∧ ∀ k < r.size, (idxA L i r a)[k]! =
      if (∃ b ∈ List.range 5, (a != b) = true ∧ (L[i]!)[a]! * 693 + (L[i]!)[b]! = k) then i
      else r[k]! := by
  classical
  refine ⟨foldl_steps_size (idxB L i a)
      (fun b k => (a != b) = true ∧ (L[i]!)[a]! * 693 + (L[i]!)[b]! = k) (fun _ => i)
      (idxB_spec L i a) (List.range 5) r, fun k hk => ?_⟩
  exact foldl_steps_const (idxB L i a)
    (fun b k => (a != b) = true ∧ (L[i]!)[a]! * 693 + (L[i]!)[b]! = k) i
    (idxB_spec L i a) (List.range 5) r k hk

theorem idxI_spec (L : Array (Array Nat)) (r : Array Nat) (i : Nat) :
    (idxI L r i).size = r.size ∧
      ∀ k < r.size, (idxI L r i)[k]! = if Hit L i k then i else r[k]! := by
  classical
  have hI1 := foldl_steps_size (idxA L i)
    (fun a k => ∃ b ∈ List.range 5, (a != b) = true ∧ (L[i]!)[a]! * 693 + (L[i]!)[b]! = k)
    (fun _ => i) (fun r a => idxA_spec L i r a) (List.range 5) r
  refine ⟨hI1, fun k hk => ?_⟩
  have hI2 := foldl_steps_const (idxA L i)
    (fun a k => ∃ b ∈ List.range 5, (a != b) = true ∧ (L[i]!)[a]! * 693 + (L[i]!)[b]! = k)
    i (fun r a => idxA_spec L i r a) (List.range 5) r k hk
  have e : (∃ a ∈ List.range 5, ∃ b ∈ List.range 5, (a != b) = true ∧
      (L[i]!)[a]! * 693 + (L[i]!)[b]! = k) ↔ Hit L i k := by
    simp only [List.mem_range, bne_iff_ne, ne_eq, Hit]
  unfold idxI
  rw [hI2]
  simp only [e]

theorem lineIdx_get (L : Array (Array Nat)) {i0 k : Nat} (hi0 : i0 < L.size)
    (hk : k < 693 * 693) (hhit : Hit L i0 k) (huniq : ∀ j < L.size, Hit L j k → j = i0) :
    (lineIdx L)[k]! = i0 := by
  classical
  rw [lineIdx_eq]
  have hsize : (Array.replicate (693 * 693) L.size).size = 693 * 693 := Array.size_replicate ..
  exact foldl_steps_unique (idxI L) (fun i k => Hit L i k) (fun i => i)
    (fun r i => idxI_spec L r i) (List.range L.size) (Array.replicate (693 * 693) L.size) k i0
    (by rw [hsize]; exact hk) (List.nodup_range) (List.mem_range.2 hi0) hhit
    (fun j hj hH => huniq j (List.mem_range.1 hj) hH)

end CFSG.KC.Misc.Lines

end
