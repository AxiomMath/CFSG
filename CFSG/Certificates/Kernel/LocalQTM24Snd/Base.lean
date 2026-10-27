module

public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.Push

public section

namespace CFSG.KC.LQT.M24Snd

@[expose] def ball {α : Type*} (f : α → List α) (seeds : Set α) : ℕ → Set α
  | 0 => seeds
  | k + 1 => ball f seeds k ∪ {y | ∃ x ∈ ball f seeds k, y ∈ f x}

variable {α : Type*} {f : α → List α} {seeds : Set α}

theorem ball_zero : ball f seeds 0 = seeds := rfl

theorem mem_ball_zero {x : α} (h : x ∈ seeds) : x ∈ ball f seeds 0 := h

theorem ball_mono {j k : ℕ} (h : j ≤ k) : ball f seeds j ⊆ ball f seeds k := by
  induction k, h using Nat.le_induction with
  | base => exact fun _ hx => hx
  | succ k _ ih => exact fun x hx => Or.inl (ih hx)

theorem ball_step {k : ℕ} {x y : α} (hx : x ∈ ball f seeds k) (hy : y ∈ f x) :
    y ∈ ball f seeds (k + 1) :=
  Or.inr ⟨x, hx, hy⟩

structure BfsInv (f : α → List α) (seeds : Set α) (k : ℕ) (S F : Set α) : Prop where
  sub : ∀ x ∈ S, x ∈ ball f seeds k
  sup : ∀ x ∈ ball f seeds k, x ∈ S
  front : ∀ x ∈ ball f seeds k, (∀ j < k, x ∉ ball f seeds j) → x ∈ F
  inS : ∀ x ∈ F, x ∈ S

theorem BfsInv.init : BfsInv f seeds 0 seeds seeds :=
  ⟨fun _ hx => hx, fun _ hx => hx, fun _ hx _ => hx, fun _ hx => hx⟩

theorem BfsInv.step {k : ℕ} {S F S' F' : Set α} (h : BfsInv f seeds k S F)
    (hS' : ∀ y, y ∈ S' ↔ y ∈ S ∨ ∃ x ∈ F, y ∈ f x)
    (hF1 : ∀ y, (∃ x ∈ F, y ∈ f x) → y ∉ S → y ∈ F')
    (hF2 : ∀ y ∈ F', ∃ x ∈ F, y ∈ f x) : BfsInv f seeds (k + 1) S' F' := by
  refine ⟨fun y hy => ?_, fun y hy => ?_, fun y hy hnew => ?_, fun y hy => ?_⟩
  · rcases (hS' y).1 hy with hyS | ⟨x, hxF, hyx⟩
    · exact ball_mono (Nat.le_succ k) (h.sub y hyS)
    · exact ball_step (h.sub x (h.inS x hxF)) hyx
  · rcases hy with hyk | ⟨x, hx, hyx⟩
    · exact (hS' y).2 (Or.inl (h.sup y hyk))
    · by_cases hj : ∀ j < k, x ∉ ball f seeds j
      · exact (hS' y).2 (Or.inr ⟨x, h.front x hx hj, hyx⟩)
      · push Not at hj
        obtain ⟨j, hjk, hxj⟩ := hj
        exact (hS' y).2 (Or.inl (h.sup y (ball_mono (Nat.succ_le_of_lt hjk) (ball_step hxj hyx))))
  · have hyk : y ∉ ball f seeds k := hnew k (Nat.lt_succ_self k)
    rcases hy with hy | ⟨x, hx, hyx⟩
    · exact absurd hy hyk
    · have hxj : ∀ j < k, x ∉ ball f seeds j := fun j hj hxj =>
        hyk (ball_mono (Nat.succ_le_of_lt hj) (ball_step hxj hyx))
      exact hF1 y ⟨x, h.front x hx hxj, hyx⟩ fun hyS => hyk (h.sub y hyS)
  · obtain ⟨x, hxF, hyx⟩ := hF2 y hy
    exact (hS' y).2 (Or.inr ⟨x, hxF, hyx⟩)

theorem BfsInv.closed {k : ℕ} {S F : Set α} (h : BfsInv f seeds k S F) (hF : ∀ x, x ∉ F) :
    ∀ x ∈ S, ∀ y ∈ f x, y ∈ S := by
  intro x hx y hy
  have hxk := h.sub x hx
  cases k with
  | zero =>
    exact absurd (h.front x hxk fun j hj => absurd hj (Nat.not_lt_zero j)) (hF x)
  | succ k =>
    have hle : ball f seeds (k + 1) ⊆ ball f seeds k := by
      intro z hz
      by_contra hzk
      refine hF z (h.front z hz fun j hj hzj => hzk ?_)
      exact ball_mono (Nat.le_of_lt_succ hj) hzj
    exact h.sup y (ball_step (hle hxk) hy)

theorem ball_image {β : Type*} (φ : α → β) {f' : β → List β} {seeds' : Set β}
    (hf : ∀ x, (f x).map φ = f' (φ x)) (hs : φ '' seeds = seeds') (k : ℕ) :
    φ '' ball f seeds k = ball f' seeds' k := by
  induction k with
  | zero => exact hs
  | succ k ih =>
    ext z
    constructor
    · rintro ⟨y, hy | ⟨x, hx, hyx⟩, rfl⟩
      · exact Or.inl (ih ▸ ⟨y, hy, rfl⟩)
      · refine Or.inr ⟨φ x, ih ▸ ⟨x, hx, rfl⟩, ?_⟩
        rw [← hf x]
        exact List.mem_map_of_mem hyx
    · rintro (hz | ⟨x', hx', hzx'⟩)
      · obtain ⟨y, hy, rfl⟩ := ih ▸ hz
        exact ⟨y, Or.inl hy, rfl⟩
      · obtain ⟨x, hx, rfl⟩ := ih ▸ hx'
        rw [← hf x, List.mem_map] at hzx'
        obtain ⟨y, hy, rfl⟩ := hzx'
        exact ⟨y, Or.inr ⟨x, hx, hy⟩, rfl⟩

end CFSG.KC.LQT.M24Snd

end
