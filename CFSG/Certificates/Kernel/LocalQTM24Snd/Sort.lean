module

public import CFSG.Certificates.Kernel.LocalQTM24Snd.Base
public import Certificates.Data.Kernel.LocalQT.M24L
public import CFSG.Certificates.Kernel.LocalQTPairsCodes

public section

namespace CFSG.KC.LQT.M24Snd

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.W CFSG.KC.LQT.T2 CFSG.KC.LQT.Syl
  CFSG.KC.LQT.M24

theorem forceN_eq {β : Type} (l : List ℕ) (k : List ℕ → β) : forceN l k = k l := by
  induction l generalizing k with
  | nil => rfl
  | cons x t ih =>
    show forceN t (fun rest => Nat.rec (motive := fun _ => β) (k (List.cons 0 rest))
      (fun m _ => k (List.cons (Nat.succ m) rest)) x) = k (x :: t)
    rw [ih]
    cases x <;> rfl

private theorem aux_sort_mem_dropLt (x : ℕ) :
    ∀ (ys : List ℕ) (z : ℕ), z ∈ dropLt x ys → z ∈ ys := by
  intro ys
  induction ys with
  | nil => intro z h; exact h
  | cons y ys ih =>
    intro z h
    change z ∈ Bool.rec (motive := fun _ => List ℕ) (y :: ys) (dropLt x ys) (Nat.blt y x) at h
    revert h
    generalize Nat.blt y x = b
    cases b
    · intro h; exact h
    · intro h; exact List.mem_cons_of_mem y (ih z h)

private theorem aux_sort_head_mem (x : ℕ) (l : List ℕ)
    (h : List.rec (motive := fun _ => Bool) false (fun y _ _ => Nat.beq y x) l = true) :
    x ∈ l := by
  cases l with
  | nil => exact absurd (show (false : Bool) = true from h) (by decide)
  | cons y t =>
    have hyx : y = x := Nat.eq_of_beq_eq_true (show Nat.beq y x = true from h)
    exact List.mem_cons.2 (Or.inl hyx.symm)

private theorem aux_sort_diffS_cons (x : ℕ) (xs ys : List ℕ) :
    diffS (x :: xs) ys =
      Bool.rec (motive := fun _ => List ℕ) (x :: diffS xs (dropLt x ys)) (diffS xs (dropLt x ys))
        (List.rec (motive := fun _ => Bool) false (fun y _ _ => Nat.beq y x) (dropLt x ys)) :=
  rfl

private theorem aux_sort_mem_diffS_cons (x z : ℕ) (xs ys : List ℕ) :
    z ∈ diffS (x :: xs) ys ↔
      (z = x ∧ ¬ (List.rec (motive := fun _ => Bool) false (fun y _ _ => Nat.beq y x)
        (dropLt x ys) = true)) ∨ z ∈ diffS xs (dropLt x ys) := by
  rw [aux_sort_diffS_cons]
  generalize List.rec (motive := fun _ => Bool) false (fun y _ _ => Nat.beq y x)
    (dropLt x ys) = b
  cases b
  · show z ∈ x :: diffS xs (dropLt x ys) ↔ _
    simp [List.mem_cons]
  · show z ∈ diffS xs (dropLt x ys) ↔ _
    simp

theorem diffS_subset (xs ys : List ℕ) : ∀ y ∈ diffS xs ys, y ∈ xs := by
  induction xs generalizing ys with
  | nil => intro y hy; exact hy
  | cons x xs ih =>
    intro y hy
    rcases (aux_sort_mem_diffS_cons x y xs ys).1 hy with ⟨h, _⟩ | h
    · exact List.mem_cons.2 (Or.inl h)
    · exact List.mem_cons.2 (Or.inr (ih (dropLt x ys) y h))

theorem diffS_cover (xs ys : List ℕ) : ∀ x ∈ xs, x ∈ ys ∨ x ∈ diffS xs ys := by
  induction xs generalizing ys with
  | nil => intro x hx; simp at hx
  | cons a xs ih =>
    intro z hz
    rcases List.mem_cons.1 hz with h | h
    · rw [h]
      by_cases hd : List.rec (motive := fun _ => Bool) false (fun y _ _ => Nat.beq y a)
          (dropLt a ys) = true
      · exact Or.inl (aux_sort_mem_dropLt a ys a (aux_sort_head_mem a _ hd))
      · exact Or.inr ((aux_sort_mem_diffS_cons a a xs ys).2 (Or.inl ⟨rfl, hd⟩))
    · rcases ih (dropLt a ys) z h with h1 | h1
      · exact Or.inl (aux_sort_mem_dropLt a ys z h1)
      · exact Or.inr ((aux_sort_mem_diffS_cons a z xs ys).2 (Or.inr h1))

theorem newK_spec (f : ℕ → List ℕ) (S F : List ℕ) :
    (∀ y ∈ newK f S F, ∃ x ∈ F, y ∈ f x) ∧
      ∀ y, (∃ x ∈ F, y ∈ f x) → y ∉ S → y ∈ newK f S F := by
  constructor
  · intro y hy
    have h1 : y ∈ dedupS (sortN (List.flatten (List.map f F))) := diffS_subset _ _ y hy
    have h2 : y ∈ sortN (List.flatten (List.map f F)) :=
      (CFSG.KC.LQT.Pairs.mem_dedupS y _).1 h1
    have h3 : y ∈ List.flatten (List.map f F) :=
      (CFSG.KC.LQT.Pairs.sortN_perm (List.flatten (List.map f F))).mem_iff.1 h2
    obtain ⟨l, hl, hyl⟩ := List.mem_flatten.1 h3
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
    exact ⟨x, hx, hyl⟩
  · rintro y ⟨x, hx, hyx⟩ hyS
    have h3 : y ∈ List.flatten (List.map f F) :=
      List.mem_flatten.2 ⟨f x, List.mem_map.2 ⟨x, hx, rfl⟩, hyx⟩
    have h2 : y ∈ sortN (List.flatten (List.map f F)) :=
      (CFSG.KC.LQT.Pairs.sortN_perm (List.flatten (List.map f F))).mem_iff.2 h3
    have h1 : y ∈ dedupS (sortN (List.flatten (List.map f F))) :=
      (CFSG.KC.LQT.Pairs.mem_dedupS y _).2 h2
    rcases diffS_cover _ _ y h1 with h | h
    · exact absurd h hyS
    · exact h

theorem mergeK_mem (xs ys : List ℕ) (y : ℕ) : y ∈ mergeK xs ys ↔ y ∈ xs ∨ y ∈ ys := by
  rw [(CFSG.KC.LQT.T2.mergeK_permT xs ys).mem_iff, List.mem_append]

@[expose] noncomputable def rounds (f : ℕ → List ℕ) (r : ℕ) (S F : List ℕ) : List ℕ × List ℕ :=
  roundsK f r S F fun S' F' => (S', F')

private theorem aux_sort_roundsK_succ {β : Type} (f : ℕ → List ℕ) (r : ℕ) (S F : List ℕ)
    (k : List ℕ → List ℕ → β) :
    roundsK f (r + 1) S F k = roundsK f r (mergeK S (newK f S F)) (newK f S F) k := by
  show forceN (newK f S F) (fun Nw => forceN (mergeK S Nw) (fun S' => roundsK f r S' Nw k)) =
    roundsK f r (mergeK S (newK f S F)) (newK f S F) k
  simp only [forceN_eq]

private theorem aux_sort_rounds_succ (f : ℕ → List ℕ) (r : ℕ) (S F : List ℕ) :
    rounds f (r + 1) S F = rounds f r (mergeK S (newK f S F)) (newK f S F) :=
  aux_sort_roundsK_succ f r S F (fun S' F' => (S', F'))

theorem roundsK_eq {β : Type} (f : ℕ → List ℕ) (r : ℕ) (S F : List ℕ)
    (k : List ℕ → List ℕ → β) :
    roundsK f r S F k = k (rounds f r S F).1 (rounds f r S F).2 := by
  induction r generalizing S F with
  | zero => rfl
  | succ r ih => rw [aux_sort_roundsK_succ, ih, aux_sort_rounds_succ]

theorem rounds_succ (f : ℕ → List ℕ) (r : ℕ) (S F : List ℕ) :
    rounds f (r + 1) S F = rounds f r (mergeK S (newK f S F)) (newK f S F) :=
  aux_sort_rounds_succ f r S F

private theorem aux_sort_step_S (f : ℕ → List ℕ) (S F : List ℕ) (y : ℕ) :
    y ∈ mergeK S (newK f S F) ↔ (y ∈ S ∨ ∃ x ∈ F, y ∈ f x) := by
  rw [mergeK_mem]
  constructor
  · rintro (hy | hy)
    · exact Or.inl hy
    · exact Or.inr ((newK_spec f S F).1 y hy)
  · rintro (hy | ⟨x, hx, hyx⟩)
    · exact Or.inl hy
    · by_cases hyS : y ∈ S
      · exact Or.inl hyS
      · exact Or.inr ((newK_spec f S F).2 y ⟨x, hx, hyx⟩ hyS)

theorem rounds_inv (f : ℕ → List ℕ) (seeds : Set ℕ) (k : ℕ) (S F : List ℕ)
    (h : BfsInv f seeds k {x | x ∈ S} {x | x ∈ F}) (r : ℕ) :
    BfsInv f seeds (k + r) {x | x ∈ (rounds f r S F).1} {x | x ∈ (rounds f r S F).2} := by
  induction r generalizing k S F with
  | zero => exact h
  | succ r ih =>
    rw [rounds_succ]
    have hstep : BfsInv f seeds (k + 1) {x | x ∈ mergeK S (newK f S F)}
        {x | x ∈ newK f S F} :=
      BfsInv.step h (fun y => aux_sort_step_S f S F y)
        (fun y hy hyS => (newK_spec f S F).2 y hy hyS) (fun y hy => (newK_spec f S F).1 y hy)
    rw [show k + (r + 1) = k + 1 + r by omega]
    exact ih (k + 1) (mergeK S (newK f S F)) (newK f S F) hstep

theorem bfsC_inv (n : ℕ) (gens : List ℕ) (r : ℕ) :
    BfsInv (fun x => gens.map (mul n x)) {one n} r
      {x | x ∈ (rounds (fun x => gens.map (mul n x)) r [one n] [one n]).1}
      {x | x ∈ (rounds (fun x => gens.map (mul n x)) r [one n] [one n]).2} := by
  have h0 : BfsInv (fun x => gens.map (mul n x)) ({one n} : Set ℕ) 0
      {x | x ∈ [one n]} {x | x ∈ [one n]} := by
    have e : ({x | x ∈ [one n]} : Set ℕ) = {one n} := by
      ext x
      simp
    rw [e]
    exact BfsInv.init
  have := rounds_inv (fun x => gens.map (mul n x)) {one n} 0 [one n] [one n] h0 r
  rwa [Nat.zero_add] at this

theorem bfsC_eq {β : Type} (n : ℕ) (gens : List ℕ) (r : ℕ) (S F : List ℕ)
    (k : List ℕ → List ℕ → β) :
    bfsC n gens r S F k =
      k (rounds (fun x => gens.map (mul n x)) r S F).1
        (rounds (fun x => gens.map (mul n x)) r S F).2 :=
  roundsK_eq _ r S F k

private theorem aux_sort_nilK_iff (l : List ℕ) : nilK l = true ↔ l = [] := by
  cases l with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons a t =>
    exact ⟨fun h => absurd (show (false : Bool) = true from h) (by decide),
      fun h => absurd h (List.cons_ne_nil a t)⟩

theorem closedK_spec (n : ℕ) (gens S : List ℕ) (h : closedK n gens S = true) :
    ∀ x ∈ S, ∀ g ∈ gens, mul n x g ∈ S := by
  intro x hx g hg
  by_contra hS
  have hL : nilK (newK (fun x => List.map (mul n x) gens) S S) = true := h
  have hnil : newK (fun x => List.map (mul n x) gens) S S = [] := (aux_sort_nilK_iff _).1 hL
  have hmem : mul n x g ∈ newK (fun x => List.map (mul n x) gens) S S :=
    (newK_spec (fun x => List.map (mul n x) gens) S S).2 (mul n x g)
      ⟨x, hx, List.mem_map.2 ⟨g, hg, rfl⟩⟩ hS
  rw [hnil] at hmem
  simp at hmem

end CFSG.KC.LQT.M24Snd

end
