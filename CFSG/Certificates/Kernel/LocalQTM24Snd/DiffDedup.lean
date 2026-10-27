module

public import CFSG.Certificates.Kernel.LocalQTPairsCodes

public section

namespace CFSG.KC.LQT.M24Snd

open CFSG.KC.LQT.Syl
open CFSG.KC.LQT.Pairs (dedGo)

private theorem aux_subb_dedGo_nil (o : Option ℕ) : dedGo [] o = [] := rfl

private theorem aux_subb_dedGo_cons_none (x : ℕ) (l : List ℕ) :
    dedGo (x :: l) none = x :: dedGo l (some x) := rfl

private theorem aux_subb_dedGo_cons_some (x y : ℕ) (l : List ℕ) :
    dedGo (x :: l) (some y) = if x = y then dedGo l (some x) else x :: dedGo l (some x) := by
  show Bool.rec (motive := fun _ => List ℕ) (x :: dedGo l (some x)) (dedGo l (some x))
    (Nat.beq x y) = _
  by_cases h : x = y
  · rw [if_pos h, Nat.beq_eq.mpr h] <;> rfl
  · have hb : Nat.beq x y = false := Bool.eq_false_iff.mpr (fun e => h (Nat.eq_of_beq_eq_true e))
    rw [if_neg h, hb] <;> rfl

private theorem aux_subb_dedGo_strict : ∀ (l : List ℕ) (o : Option ℕ),
    l.Pairwise (· ≤ ·) → (∀ y, o = some y → ∀ z ∈ l, y ≤ z) →
      (dedGo l o).Pairwise (· < ·) ∧ (∀ y, o = some y → ∀ z ∈ dedGo l o, y < z)
  | [], o, _, _ => by
    rw [aux_subb_dedGo_nil]
    exact ⟨List.Pairwise.nil, fun _ _ _ hz => absurd hz List.not_mem_nil⟩
  | x :: l, o, hl, ho => by
    obtain ⟨hxl, hl'⟩ := List.pairwise_cons.mp hl
    have h := aux_subb_dedGo_strict l (some x) hl' (fun y' hy' z hz => by
      obtain rfl := Option.some.inj hy'
      exact hxl z hz)
    cases o with
    | none =>
      rw [aux_subb_dedGo_cons_none]
      exact ⟨List.pairwise_cons.mpr ⟨fun z hz => h.2 x rfl z hz, h.1⟩, fun _ hy => by cases hy⟩
    | some y =>
      have hyx : y ≤ x := ho y rfl x (by simp)
      rw [aux_subb_dedGo_cons_some]
      by_cases hxy : x = y
      · rw [if_pos hxy]
        refine ⟨h.1, fun y' hy' z hz => ?_⟩
        obtain rfl := Option.some.inj hy'
        have := h.2 x rfl z hz
        omega
      · rw [if_neg hxy]
        have hlt : y < x := lt_of_le_of_ne hyx (fun e => hxy e.symm)
        refine ⟨List.pairwise_cons.mpr ⟨fun z hz => h.2 x rfl z hz, h.1⟩, fun y' hy' z hz => ?_⟩
        obtain rfl := Option.some.inj hy'
        rcases List.mem_cons.mp hz with h1 | h1
        · omega
        · have := h.2 x rfl z h1
          omega

theorem dedupS_strict {l : List ℕ} (h : l.Pairwise (· ≤ ·)) : (dedupS l).Pairwise (· < ·) :=
  (aux_subb_dedGo_strict l none h (fun _ hy => absurd hy (by simp))).1

private theorem aux_subb_dropLt_nil (x : ℕ) : dropLt x [] = [] := rfl

private theorem aux_subb_dropLt_cons (x a : ℕ) (ys : List ℕ) :
    dropLt x (a :: ys) = if a < x then dropLt x ys else a :: ys := by
  show Bool.rec (motive := fun _ => List ℕ) (a :: ys) (dropLt x ys) (Nat.blt a x) = _
  by_cases h : a < x
  · rw [if_pos h, Nat.blt_eq.mpr h] <;> rfl
  · have hb : Nat.blt a x = false := Bool.eq_false_iff.mpr (fun e => h (Nat.blt_eq.mp e))
    rw [if_neg h, hb] <;> rfl

private theorem aux_subb_dropLt_pairwise (x : ℕ) : ∀ ys : List ℕ, ys.Pairwise (· < ·) →
    (dropLt x ys).Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | a :: rest, hp => by
    rw [aux_subb_dropLt_cons]
    split
    · exact aux_subb_dropLt_pairwise x rest (List.pairwise_cons.mp hp).2
    · exact hp

private theorem aux_subb_mem_dropLt (x : ℕ) : ∀ ys : List ℕ, ys.Pairwise (· < ·) →
    ∀ z, z ∈ dropLt x ys ↔ z ∈ ys ∧ x ≤ z
  | [], _ => by
    intro z
    simp [aux_subb_dropLt_nil]
  | a :: rest, hp => by
    obtain ⟨hgt, hrest⟩ := List.pairwise_cons.mp hp
    have ih := aux_subb_mem_dropLt x rest hrest
    intro z
    rw [aux_subb_dropLt_cons]
    by_cases hax : a < x
    · rw [if_pos hax, ih z, List.mem_cons]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨Or.inr h1, h2⟩
      · rintro ⟨h1 | h1, h2⟩
        · exfalso
          omega
        · exact ⟨h1, h2⟩
    · rw [if_neg hax, List.mem_cons]
      constructor
      · rintro (h1 | h1)
        · exact ⟨Or.inl h1, by omega⟩
        · exact ⟨Or.inr h1, by have := hgt z h1; omega⟩
      · rintro ⟨h1 | h1, _⟩
        · exact Or.inl h1
        · exact Or.inr h1

private theorem aux_subb_head_iff (x : ℕ) : ∀ ys : List ℕ, ys.Pairwise (· < ·) →
    (List.rec (motive := fun _ => Bool) false (fun y _ _ => Nat.beq y x) (dropLt x ys) = true
      ↔ x ∈ ys)
  | [], _ => by
    rw [aux_subb_dropLt_nil]
    simp
  | a :: rest, hp => by
    obtain ⟨hgt, hrest⟩ := List.pairwise_cons.mp hp
    have ih := aux_subb_head_iff x rest hrest
    rw [aux_subb_dropLt_cons]
    by_cases hax : a < x
    · rw [if_pos hax, List.mem_cons]
      constructor
      · intro h
        exact Or.inr (ih.1 h)
      · rintro (h1 | h1)
        · exfalso
          omega
        · exact ih.2 h1
    · rw [if_neg hax]
      show Nat.beq a x = true ↔ x ∈ a :: rest
      rw [Nat.beq_eq, List.mem_cons]
      constructor
      · intro h
        exact Or.inl h.symm
      · rintro (h1 | h1)
        · exact h1.symm
        · exact absurd (hgt x h1) hax

private theorem aux_subb_diffS_cons (x : ℕ) (xs ys : List ℕ) (hy : ys.Pairwise (· < ·)) :
    diffS (x :: xs) ys =
      if x ∈ ys then diffS xs (dropLt x ys) else x :: diffS xs (dropLt x ys) := by
  have hb := aux_subb_head_iff x ys hy
  show Bool.rec (motive := fun _ => List ℕ) (x :: diffS xs (dropLt x ys))
      (diffS xs (dropLt x ys))
      (List.rec (motive := fun _ => Bool) false (fun y _ _ => Nat.beq y x) (dropLt x ys)) = _
  by_cases hxy : x ∈ ys
  · rw [if_pos hxy, hb.2 hxy] <;> rfl
  · have hf : List.rec (motive := fun _ => Bool) false (fun y _ _ => Nat.beq y x)
        (dropLt x ys) = false :=
      Bool.eq_false_iff.mpr (fun h => hxy (hb.1 h))
    rw [if_neg hxy, hf] <;> rfl

private theorem aux_subb_diff_main : ∀ (xs ys : List ℕ), xs.Pairwise (· < ·) →
    ys.Pairwise (· < ·) → diffS xs ys = xs.filter (fun x => decide (x ∉ ys))
  | [], _, _, _ => rfl
  | x :: xs, ys, hx, hy => by
    obtain ⟨hgt, hxs⟩ := List.pairwise_cons.mp hx
    have hD := aux_subb_diff_main xs (dropLt x ys) hxs (aux_subb_dropLt_pairwise x ys hy)
    have hcongr : xs.filter (fun z => decide (z ∉ dropLt x ys)) =
        xs.filter (fun z => decide (z ∉ ys)) := by
      apply List.filter_congr
      intro z hz
      have hxz : x < z := hgt z hz
      have hiff : z ∉ dropLt x ys ↔ z ∉ ys := by
        rw [aux_subb_mem_dropLt x ys hy z]
        constructor
        · intro h hz'
          exact h ⟨hz', le_of_lt hxz⟩
        · intro h hz'
          exact h hz'.1
      exact decide_eq_decide.mpr hiff
    rw [aux_subb_diffS_cons x xs ys hy, hD, hcongr, List.filter_cons]
    by_cases hxm : x ∈ ys
    · simp [hxm]
    · simp [hxm]

theorem diffS_eq_filter {xs ys : List ℕ} (hx : xs.Pairwise (· < ·)) (hy : ys.Pairwise (· < ·)) :
    diffS xs ys = xs.filter (fun x => decide (x ∉ ys)) :=
  aux_subb_diff_main xs ys hx hy

end CFSG.KC.LQT.M24Snd

end
