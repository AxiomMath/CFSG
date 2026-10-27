module

public import CFSG.Sporadic.Mathieu.M12

public section

namespace CFSG.ComponentClassification.M12Cover

open CFSG.Blueprint CFSG.Sporadic.Mathieu

@[expose] def permOfImages (v w : Fin 12 → Fin 12) (h₁ : ∀ i, w (v i) = i)
    (h₂ : ∀ i, v (w i) = i) : Equiv.Perm (Fin 12) :=
  ⟨v, w, h₁, h₂⟩

@[expose] def s₁ : Equiv.Perm (Fin 12) :=
  permOfImages ![2, 3, 0, 1, 5, 4, 11, 9, 10, 7, 8, 6] ![2, 3, 0, 1, 5, 4, 11, 9, 10, 7, 8, 6]
    (by decide) (by decide)

@[expose] def s₂ : Equiv.Perm (Fin 12) :=
  permOfImages ![1, 0, 4, 11, 2, 6, 5, 9, 10, 7, 8, 3] ![1, 0, 4, 11, 2, 6, 5, 9, 10, 7, 8, 3]
    (by decide) (by decide)

@[expose] def s₃ : Equiv.Perm (Fin 12) :=
  permOfImages ![4, 2, 5, 0, 6, 11, 3, 9, 10, 7, 8, 1] ![3, 11, 1, 6, 0, 2, 4, 9, 10, 7, 8, 5]
    (by decide) (by decide)

@[expose] def s₄ : Equiv.Perm (Fin 12) :=
  permOfImages ![1, 0, 2, 4, 3, 6, 5, 10, 8, 9, 7, 11] ![1, 0, 2, 4, 3, 6, 5, 10, 8, 9, 7, 11]
    (by decide) (by decide)

@[expose] def S : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure {s₁, s₂, s₃, s₄}

theorem s₁_mem_S : s₁ ∈ S := Subgroup.subset_closure (by simp)

theorem s₂_mem_S : s₂ ∈ S := Subgroup.subset_closure (by simp)

theorem s₃_mem_S : s₃ ∈ S := Subgroup.subset_closure (by simp)

theorem s₄_mem_S : s₄ ∈ S := Subgroup.subset_closure (by simp)

namespace SylowTable

@[expose] def nth {α : Type*} (d : α) : List α → ℕ → α
  | [], _ => d
  | a :: _, 0 => a
  | _ :: l, k + 1 => nth d l k

theorem nth_map {α β : Type*} (d : α) (d' : β) (F : α → β) :
    ∀ (l : List α) (k : ℕ), k < l.length → nth d' (l.map F) k = F (nth d l k)
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: l, k + 1, h => nth_map d d' F l k (Nat.lt_of_succ_lt_succ h)

theorem nth_of_length_le {α : Type*} (d : α) : ∀ (l : List α) (k : ℕ), l.length ≤ k → nth d l k = d
  | [], _, _ => rfl
  | _ :: _, 0, h => absurd h (by simp)
  | _ :: l, k + 1, h => nth_of_length_le d l k (by simpa using h)

theorem eq_of_nth {α : Type*} (d : α) : ∀ (l l' : List α), l.length = l'.length →
    (∀ k < l.length, nth d l k = nth d l' k) → l = l'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => absurd h (by simp)
  | _ :: _, [], h, _ => absurd h (by simp)
  | a :: l, a' :: l', hlen, h => by
    have h0 : a = a' := h 0 (by simp)
    rw [h0, eq_of_nth d l l' (by simpa using hlen) fun k hk => h (k + 1) (by simpa using hk)]

@[expose] def IsCode (c : List ℕ) (σ : Equiv.Perm (Fin 12)) : Prop :=
  c.length = 12 ∧ ∀ p : Fin 12, nth 0 c p = σ p

@[expose] def comp (c d : List ℕ) : List ℕ := d.map (nth 0 c)

theorem IsCode.mul {c d : List ℕ} {σ τ : Equiv.Perm (Fin 12)} (hc : IsCode c σ)
    (hd : IsCode d τ) : IsCode (comp c d) (σ * τ) := by
  refine ⟨by rw [comp, List.length_map, hd.1], fun p => ?_⟩
  rw [comp, nth_map 0 0 _ d p (by rw [hd.1]; exact p.2), hd.2 p, Equiv.Perm.mul_apply]
  exact hc.2 (τ p)

theorem IsCode.perm_eq {c : List ℕ} {σ τ : Equiv.Perm (Fin 12)} (h : IsCode c σ)
    (h' : IsCode c τ) : σ = τ :=
  Equiv.ext fun p => Fin.ext ((h.2 p).symm.trans (h'.2 p))

theorem IsCode.code_eq {c d : List ℕ} {σ : Equiv.Perm (Fin 12)} (h : IsCode c σ)
    (h' : IsCode d σ) : c = d :=
  eq_of_nth 0 c d (by rw [h.1, h'.1]) fun k hk => by
    rw [h.1] at hk
    exact (h.2 ⟨k, hk⟩).trans (h'.2 ⟨k, hk⟩).symm

theorem isCode_one : IsCode (List.range 12) 1 := ⟨by simp, by decide⟩

theorem isCode_s₁ : IsCode [2, 3, 0, 1, 5, 4, 11, 9, 10, 7, 8, 6] s₁ := ⟨rfl, by decide⟩

theorem isCode_s₂ : IsCode [1, 0, 4, 11, 2, 6, 5, 9, 10, 7, 8, 3] s₂ := ⟨rfl, by decide⟩

theorem isCode_s₃ : IsCode [4, 2, 5, 0, 6, 11, 3, 9, 10, 7, 8, 1] s₃ := ⟨rfl, by decide⟩

theorem isCode_s₄ : IsCode [1, 0, 2, 4, 3, 6, 5, 10, 8, 9, 7, 11] s₄ := ⟨rfl, by decide⟩

def m12Letter (k : ℕ) : Equiv.Perm (Fin 12) := if k = 0 then m12gA else m12gB

def m12Word (w : List ℕ) : Equiv.Perm (Fin 12) := (w.map m12Letter).prod

def letterCode (k : ℕ) : List ℕ :=
  if k = 0 then [3, 1, 9, 0, 10, 11, 6, 7, 8, 2, 4, 5] else [7, 2, 3, 1, 11, 9, 5, 8, 0, 6, 4, 10]

def wordCode (w : List ℕ) : List ℕ := w.foldr (fun k c => comp (letterCode k) c) (List.range 12)

theorem isCode_letter (k : ℕ) : IsCode (letterCode k) (m12Letter k) := by
  unfold letterCode m12Letter
  split_ifs
  · exact ⟨rfl, by decide⟩
  · exact ⟨rfl, by decide⟩

theorem isCode_m12Word : ∀ w : List ℕ, IsCode (wordCode w) (m12Word w)
  | [] => isCode_one
  | k :: w => by
    change IsCode (comp (letterCode k) (wordCode w)) (m12Letter k * m12Word w)
    exact (isCode_letter k).mul (isCode_m12Word w)

theorem m12Word_mem (w : List ℕ) : m12Word w ∈ NativeSporadic.M12 := by
  refine list_prod_mem fun x hx => ?_
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
  unfold m12Letter
  split_ifs
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem mem_M12_of_isCode {c : List ℕ} {σ : Equiv.Perm (Fin 12)} (hσ : IsCode c σ) (w : List ℕ)
    (hw : wordCode w = c) : σ ∈ NativeSporadic.M12 := by
  rw [hσ.perm_eq (hw ▸ isCode_m12Word w)]
  exact m12Word_mem w

@[expose] def codeT : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [2, 3, 0, 1, 5, 4, 11, 9, 10, 7, 8, 6],
   [1, 0, 4, 11, 2, 6, 5, 9, 10, 7, 8, 3], [1, 0, 2, 4, 3, 6, 5, 10, 8, 9, 7, 11],
   [4, 11, 1, 0, 6, 2, 3, 7, 8, 9, 10, 5], [2, 4, 1, 0, 6, 3, 11, 9, 7, 10, 8, 5],
   [3, 2, 5, 6, 0, 11, 4, 7, 8, 9, 10, 1], [0, 1, 3, 11, 2, 5, 6, 9, 7, 10, 8, 4],
   [3, 2, 0, 5, 1, 11, 4, 8, 10, 7, 9, 6], [0, 1, 4, 2, 11, 5, 6, 8, 10, 7, 9, 3],
   [5, 6, 3, 2, 11, 0, 1, 9, 10, 7, 8, 4], [3, 11, 0, 1, 5, 2, 4, 10, 8, 9, 7, 6],
   [0, 5, 3, 2, 11, 1, 6, 7, 9, 8, 10, 4], [4, 2, 0, 1, 5, 11, 3, 7, 9, 8, 10, 6],
   [11, 4, 6, 5, 1, 3, 2, 9, 10, 7, 8, 0], [4, 2, 6, 5, 1, 11, 3, 10, 8, 9, 7, 0],
   [2, 3, 1, 6, 0, 4, 11, 7, 9, 8, 10, 5], [1, 0, 11, 3, 4, 6, 5, 7, 9, 8, 10, 2],
   [11, 4, 1, 6, 0, 3, 2, 10, 8, 9, 7, 5], [4, 2, 1, 6, 0, 11, 3, 8, 7, 10, 9, 5],
   [2, 3, 5, 0, 6, 4, 11, 10, 8, 9, 7, 1], [1, 0, 3, 2, 11, 6, 5, 8, 7, 10, 9, 4],
   [6, 5, 11, 4, 3, 1, 0, 7, 8, 9, 10, 2], [6, 5, 4, 2, 11, 1, 0, 9, 7, 10, 8, 3],
   [1, 6, 2, 3, 4, 0, 5, 8, 10, 7, 9, 11], [11, 3, 1, 0, 6, 4, 2, 8, 10, 7, 9, 5],
   [1, 6, 11, 4, 3, 0, 5, 9, 7, 10, 8, 2], [1, 6, 4, 2, 11, 0, 5, 10, 9, 8, 7, 3],
   [5, 0, 2, 3, 4, 6, 1, 9, 7, 10, 8, 11], [3, 2, 1, 0, 6, 11, 4, 10, 9, 8, 7, 5],
   [11, 3, 5, 6, 0, 4, 2, 9, 7, 10, 8, 1], [5, 0, 11, 4, 3, 6, 1, 8, 10, 7, 9, 2],
   [2, 4, 5, 6, 0, 3, 11, 8, 10, 7, 9, 1], [4, 11, 0, 5, 1, 2, 3, 9, 7, 10, 8, 6],
   [2, 4, 0, 5, 1, 3, 11, 10, 9, 8, 7, 6], [3, 2, 6, 1, 5, 11, 4, 9, 7, 10, 8, 0],
   [0, 1, 11, 4, 3, 5, 6, 10, 9, 8, 7, 2], [6, 5, 3, 11, 2, 1, 0, 8, 10, 7, 9, 4],
   [11, 3, 0, 5, 1, 4, 2, 7, 8, 9, 10, 6], [5, 0, 3, 11, 2, 6, 1, 10, 9, 8, 7, 4],
   [4, 11, 6, 1, 5, 2, 3, 8, 10, 7, 9, 0], [2, 4, 6, 1, 5, 3, 11, 7, 8, 9, 10, 0],
   [5, 6, 11, 3, 4, 0, 1, 10, 8, 9, 7, 2], [11, 4, 5, 0, 6, 3, 2, 7, 9, 8, 10, 1],
   [5, 6, 2, 4, 3, 0, 1, 7, 9, 8, 10, 11], [0, 5, 4, 11, 2, 1, 6, 10, 8, 9, 7, 3],
   [0, 5, 2, 4, 3, 1, 6, 8, 7, 10, 9, 11], [6, 1, 3, 2, 11, 5, 0, 10, 8, 9, 7, 4],
   [11, 4, 0, 1, 5, 3, 2, 8, 7, 10, 9, 6], [3, 11, 6, 5, 1, 2, 4, 7, 9, 8, 10, 0],
   [0, 5, 11, 3, 4, 1, 6, 9, 10, 7, 8, 2], [3, 11, 5, 0, 6, 2, 4, 8, 7, 10, 9, 1],
   [6, 1, 4, 11, 2, 5, 0, 7, 9, 8, 10, 3], [6, 1, 2, 4, 3, 5, 0, 9, 10, 7, 8, 11],
   [6, 1, 11, 3, 4, 5, 0, 8, 7, 10, 9, 2], [2, 3, 6, 5, 1, 4, 11, 8, 7, 10, 9, 0],
   [3, 11, 1, 6, 0, 2, 4, 9, 10, 7, 8, 5], [4, 2, 5, 0, 6, 11, 3, 9, 10, 7, 8, 1],
   [5, 6, 4, 11, 2, 0, 1, 8, 7, 10, 9, 3], [11, 3, 6, 1, 5, 4, 2, 10, 9, 8, 7, 0],
   [6, 5, 2, 3, 4, 1, 0, 10, 9, 8, 7, 11], [1, 6, 3, 11, 2, 0, 5, 7, 8, 9, 10, 4],
   [5, 0, 4, 2, 11, 6, 1, 7, 8, 9, 10, 3], [4, 11, 5, 6, 0, 2, 3, 10, 9, 8, 7, 1]]

@[expose] def genT : List ℕ :=
  [0, 0, 1, 2, 1, 2, 0, 2, 0, 1, 0, 2, 0, 1, 1, 2, 0, 1, 1, 2, 0, 2, 1, 2, 0, 1, 1, 2, 0, 2, 2, 0,
   1, 1, 2, 0, 2, 0, 2, 0, 1, 2, 2, 0, 1, 1, 2, 0, 2, 0, 2, 0, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]

@[expose] def parT : List ℕ :=
  [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13,
   14, 15, 15, 16, 16, 17, 17, 18, 18, 19, 20, 20, 22, 23, 23, 24, 24, 25, 25, 26, 26, 27, 28, 28,
   31, 32, 33, 35, 37, 43, 44, 45, 47, 49]

@[expose] def lT : List (List ℕ) :=
  [[1, 0, 6, 8, 10, 12, 2, 16, 3, 20, 4, 24, 5, 28, 22, 31, 7, 35, 37, 39, 9, 29, 14, 43, 11, 47,
    49, 51, 13, 21, 52, 15, 45, 44, 46, 17, 55, 18, 53, 19, 42, 50, 40, 23, 33, 32, 34, 25, 60, 26,
    41, 27, 30, 38, 59, 36, 61, 62, 63, 54, 48, 56, 57, 58],
   [2, 4, 0, 9, 1, 13, 14, 17, 18, 3, 22, 25, 26, 5, 6, 32, 33, 7, 8, 34, 40, 36, 10, 44, 45, 11,
    12, 46, 52, 48, 49, 47, 15, 16, 19, 43, 21, 42, 56, 54, 20, 57, 37, 35, 23, 24, 27, 31, 29, 30,
    61, 59, 28, 62, 39, 63, 38, 41, 60, 51, 58, 50, 53, 55],
   [3, 5, 7, 0, 11, 1, 15, 2, 19, 21, 23, 4, 27, 29, 30, 6, 34, 36, 38, 8, 41, 9, 42, 10, 46, 48,
    50, 12, 53, 13, 14, 54, 55, 56, 16, 57, 17, 58, 18, 52, 51, 20, 22, 59, 60, 61, 24, 62, 25, 63,
    26, 40, 39, 28, 31, 32, 33, 35, 37, 43, 44, 45, 47, 49]]

@[expose] def invT : List ℕ :=
  [0, 1, 2, 3, 6, 8, 4, 9, 5, 7, 10, 20, 12, 16, 14, 18, 13, 17, 15, 19, 11, 21, 22, 37, 28, 35, 31,
   39, 24, 29, 40, 26, 33, 32, 34, 25, 36, 23, 41, 27, 30, 38, 42, 49, 44, 45, 46, 47, 55, 43, 50,
   51, 52, 53, 54, 48, 57, 56, 58, 59, 60, 62, 61, 63]

@[expose] def code (x : ℕ) : List ℕ := nth [] codeT x

@[expose] def gen (x : ℕ) : ℕ := nth 0 genT x

@[expose] def par (x : ℕ) : ℕ := nth 0 parT x

@[expose] def lmul (i b : ℕ) : ℕ := nth 0 (nth [] lT i) b

@[expose] def invIdx (x : ℕ) : ℕ := nth 0 invT x

@[expose] def y (i : ℕ) : S :=
  if i = 0 then ⟨s₁, s₁_mem_S⟩ else if i = 1 then ⟨s₂, s₂_mem_S⟩ else ⟨s₄, s₄_mem_S⟩

@[expose] def yCode (i : ℕ) : List ℕ :=
  if i = 0 then [2, 3, 0, 1, 5, 4, 11, 9, 10, 7, 8, 6]
  else if i = 1 then [1, 0, 4, 11, 2, 6, 5, 9, 10, 7, 8, 3]
  else [1, 0, 2, 4, 3, 6, 5, 10, 8, 9, 7, 11]

theorem isCode_y (i : ℕ) : IsCode (yCode i) (y i : Equiv.Perm (Fin 12)) := by
  unfold yCode y
  split_ifs
  exacts [isCode_s₁, isCode_s₂, isCode_s₄]

@[expose] def pathAux : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, x => if x = 0 then [] else x :: pathAux n (par x)

@[expose] def path (x : ℕ) : List ℕ := pathAux 64 x

@[expose] def elt (x : ℕ) : S := ((path x).map fun z => y (gen z)).prod

@[expose] def mulIdx (a b : ℕ) : ℕ := (path a).foldr (fun z acc => lmul (gen z) acc) b

def treeCheck : Bool :=
  code 0 == List.range 12 && (List.range 64).all fun x =>
    x == 0 || (decide (par x < x) && decide (gen x < 3) &&
      code x == comp (yCode (gen x)) (code (par x)))

def lmulCheck : Bool :=
  (List.range 3).all fun i => (List.range 64).all fun b =>
    decide (lmul i b < 64) && code (lmul i b) == comp (yCode i) (code b)

def injCheck : Bool :=
  (List.range 64).all fun a => (List.range 64).all fun b => a == b || code a != code b

def invCheck : Bool :=
  (List.range 64).all fun a => decide (invIdx a < 64) && mulIdx a (invIdx a) == 0

theorem treeCheck_eq : treeCheck = true := by decide +kernel

theorem lmulCheck_eq : lmulCheck = true := by decide +kernel

theorem injCheck_eq : injCheck = true := by decide +kernel

theorem code_zero : code 0 = List.range 12 := by
  have h := treeCheck_eq
  simp only [treeCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem tree_spec {x : ℕ} (hx0 : x ≠ 0) (hx : x < 64) :
    par x < x ∧ gen x < 3 ∧ code x = comp (yCode (gen x)) (code (par x)) := by
  have h := treeCheck_eq
  simp only [treeCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have := h.2 x hx
  simp only [Bool.or_eq_true, beq_iff_eq, hx0, false_or, Bool.and_eq_true, decide_eq_true_eq]
    at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem par_lt {x : ℕ} (hx0 : x ≠ 0) : par x < x := by
  by_cases hx : x < 64
  · exact (tree_spec hx0 hx).1
  · rw [par, nth_of_length_le _ _ _ (by simp [parT]; omega)]
    omega

theorem pathAux_succ {n x : ℕ} (hx : x ≠ 0) : pathAux (n + 1) x = x :: pathAux n (par x) := by
  simp only [pathAux, hx, ↓reduceIte]

theorem pathAux_stable : ∀ n x, x < n → pathAux (n + 1) x = pathAux n x
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, x, h => by
    by_cases hx : x = 0
    · simp [pathAux, hx]
    · rw [pathAux_succ hx, pathAux_succ hx, pathAux_stable n (par x) (by have := par_lt hx; omega)]

theorem path_zero : path 0 = [] := by simp [path, pathAux]

theorem path_cons {x : ℕ} (hx0 : x ≠ 0) (hx : x < 64) : path x = x :: path (par x) := by
  have hp := par_lt hx0
  rw [path, path, pathAux_stable 63 (par x) (by omega), pathAux_succ hx0]

theorem mem_pathAux : ∀ {n x z : ℕ}, z ∈ pathAux n x → z ≠ 0 ∧ z ≤ x
  | 0, _, _, h => by simp [pathAux] at h
  | n + 1, x, z, h => by
    by_cases hx : x = 0
    · simp [pathAux, hx] at h
    · rw [pathAux_succ hx, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨hx, le_rfl⟩
      · obtain ⟨h1, h2⟩ := mem_pathAux h
        exact ⟨h1, h2.trans (par_lt hx).le⟩

theorem elt_zero : elt 0 = 1 := by simp [elt, path_zero]

theorem elt_cons {x : ℕ} (hx0 : x ≠ 0) (hx : x < 64) : elt x = y (gen x) * elt (par x) := by
  rw [elt, path_cons hx0 hx, List.map_cons, List.prod_cons]
  rfl

theorem isCode_elt : ∀ x, x < 64 → IsCode (code x) (elt x : Equiv.Perm (Fin 12)) := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hx
    by_cases hx0 : x = 0
    · subst hx0
      rw [elt_zero, code_zero]
      exact isCode_one
    · obtain ⟨hp, -, hc⟩ := tree_spec hx0 hx
      rw [elt_cons hx0 hx, hc, Subgroup.coe_mul]
      exact (isCode_y _).mul (ih _ hp (hp.trans hx))

theorem lmul_spec {i b : ℕ} (hi : i < 3) (hb : b < 64) :
    lmul i b < 64 ∧ elt (lmul i b) = y i * elt b := by
  have h := lmulCheck_eq
  simp only [lmulCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨hlt, hc⟩ := h i hi b hb
  refine ⟨hlt, Subtype.ext ?_⟩
  have h1 := isCode_elt _ hlt
  rw [hc] at h1
  rw [Subgroup.coe_mul]
  exact h1.perm_eq ((isCode_y i).mul (isCode_elt b hb))

theorem foldr_lmul_spec : ∀ (l : List ℕ), (∀ z ∈ l, gen z < 3) → ∀ b, b < 64 →
    l.foldr (fun z acc => lmul (gen z) acc) b < 64 ∧
      elt (l.foldr (fun z acc => lmul (gen z) acc) b) = (l.map fun z => y (gen z)).prod * elt b
  | [], _, b, hb => ⟨hb, by simp⟩
  | z :: l, hl, b, hb => by
    obtain ⟨h1, h2⟩ := foldr_lmul_spec l (fun z hz => hl z (List.mem_cons_of_mem _ hz)) b hb
    obtain ⟨h3, h4⟩ := lmul_spec (hl z (List.mem_cons_self ..)) h1
    refine ⟨h3, ?_⟩
    rw [List.foldr_cons, h4, h2, List.map_cons, List.prod_cons, mul_assoc]

theorem gen_lt_of_mem_path {a z : ℕ} (ha : a < 64) (hz : z ∈ path a) : gen z < 3 := by
  obtain ⟨h1, h2⟩ := mem_pathAux hz
  exact (tree_spec h1 (by omega)).2.1

theorem mulIdx_spec {a b : ℕ} (ha : a < 64) (hb : b < 64) :
    mulIdx a b < 64 ∧ elt (mulIdx a b) = elt a * elt b :=
  foldr_lmul_spec (path a) (fun _ hz => gen_lt_of_mem_path ha hz) b hb

theorem invCheck_eq : invCheck = true := by decide +kernel

theorem elt_injective {a b : ℕ} (ha : a < 64) (hb : b < 64) (h : elt a = elt b) : a = b := by
  have hc : code a = code b :=
    (isCode_elt a ha).code_eq (by rw [h]; exact isCode_elt b hb)
  have h' := injCheck_eq
  simp only [injCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq] at h'
  exact (h' a ha b hb).resolve_right (not_not.2 hc)

theorem elt_inv {a : ℕ} (ha : a < 64) : invIdx a < 64 ∧ (elt a)⁻¹ = elt (invIdx a) := by
  have h := invCheck_eq
  simp only [invCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨hlt, h0⟩ := h a ha
  refine ⟨hlt, inv_eq_of_mul_eq_one_right ?_⟩
  rw [← (mulIdx_spec ha hlt).2, h0, elt_zero]

theorem elt_eq_of_code {x : ℕ} (hx : x < 64) {σ : Equiv.Perm (Fin 12)} (c : List ℕ)
    (hσ : IsCode c σ) (hc : code x = c) : (elt x : Equiv.Perm (Fin 12)) = σ :=
  (hc ▸ isCode_elt x hx).perm_eq hσ

theorem exists_elt {σ : Equiv.Perm (Fin 12)} (hσ : σ ∈ S) :
    ∃ x, x < 64 ∧ (elt x : Equiv.Perm (Fin 12)) = σ := by
  induction hσ using Subgroup.closure_induction with
  | mem σ hσ =>
    rcases hσ with rfl | rfl | rfl | rfl
    · exact ⟨1, by norm_num, elt_eq_of_code (by norm_num) _ isCode_s₁ (by decide +kernel)⟩
    · exact ⟨2, by norm_num, elt_eq_of_code (by norm_num) _ isCode_s₂ (by decide +kernel)⟩
    · exact ⟨57, by norm_num, elt_eq_of_code (by norm_num) _ isCode_s₃ (by decide +kernel)⟩
    · exact ⟨3, by norm_num, elt_eq_of_code (by norm_num) _ isCode_s₄ (by decide +kernel)⟩
  | one => exact ⟨0, by norm_num, by rw [elt_zero]; rfl⟩
  | mul σ τ _ _ hσ hτ =>
    obtain ⟨a, ha, rfl⟩ := hσ
    obtain ⟨b, hb, rfl⟩ := hτ
    exact ⟨mulIdx a b, (mulIdx_spec ha hb).1, by rw [(mulIdx_spec ha hb).2, Subgroup.coe_mul]⟩
  | inv σ _ hσ =>
    obtain ⟨a, ha, rfl⟩ := hσ
    exact ⟨invIdx a, (elt_inv ha).1, by rw [← (elt_inv ha).2, Subgroup.coe_inv]⟩

theorem elt_surjective (s : S) : ∃ x, x < 64 ∧ elt x = s := by
  obtain ⟨x, hx, h⟩ := exists_elt s.2
  exact ⟨x, hx, Subtype.ext h⟩

theorem zmod_two_add_self (v : ZMod 2) : v + v = 0 := by grind

section Tree

variable (g : S → S → ZMod 2)

def val (k : ℕ) : ZMod 2 := g (y (k / 64)) (elt (k % 64))

def eval (m : ℕ) : ZMod 2 := ∑ k ∈ Finset.range 192, if m.testBit k then val g k else 0

theorem val_eq {i m : ℕ} (hm : m < 64) : val g (64 * i + m) = g (y i) (elt m) := by
  rw [val, show (64 * i + m) / 64 = i by omega, show (64 * i + m) % 64 = m by omega]

theorem eval_xor (m m' : ℕ) : eval g (m ^^^ m') = eval g m + eval g m' := by
  rw [eval, eval, eval, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.testBit_xor]
  cases m.testBit k <;> cases m'.testBit k <;> simp [zmod_two_add_self]

theorem eval_two_pow {j : ℕ} (hj : j < 192) : eval g (2 ^ j) = val g j := by
  simp only [eval, Nat.testBit_two_pow, decide_eq_true_eq]
  rw [Finset.sum_ite_eq]
  simp [hj]

theorem eval_and_eq_zero {K : ℕ} (hK : ∀ k < 192, K.testBit k = true → val g k = 0) (m : ℕ) :
    eval g (m &&& K) = 0 := by
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [Nat.testBit_and]
  cases h : K.testBit k
  · simp
  · simp [hK k (Finset.mem_range.1 hk) h]

theorem eval_eq_zero (h : ∀ k < 192, val g k = 0) (m : ℕ) : eval g m = 0 :=
  Finset.sum_eq_zero fun k hk => by simp [h k (Finset.mem_range.1 hk)]

def wmask (x h : ℕ) : ℕ :=
  (path x).foldr (fun z acc => 2 ^ (64 * gen z + mulIdx (par z) h) ^^^ acc) 0

theorem wmask_zero (h : ℕ) : wmask 0 h = 0 := by simp [wmask, path_zero]

theorem wmask_cons {x : ℕ} (hx0 : x ≠ 0) (hx : x < 64) (h : ℕ) :
    wmask x h = 2 ^ (64 * gen x + mulIdx (par x) h) ^^^ wmask (par x) h := by
  rw [wmask, path_cons hx0 hx, List.foldr_cons]
  rfl

inductive Step
  | edge (x : ℕ)
  | coc (i b h j : ℕ)
  | diag (q j : ℕ)

def Step.mask : Step → ℕ
  | .edge x => 2 ^ (64 * gen x + par x)
  | .coc i b h _ =>
    2 ^ (64 * i + b) ^^^ wmask (lmul i b) h ^^^ wmask b h ^^^ 2 ^ (64 * i + mulIdx b h)
  | .diag q _ => wmask q q

def Step.pivot : Step → ℕ
  | .edge x => 64 * gen x + par x
  | .coc _ _ _ j => j
  | .diag _ j => j

def Step.valid : Step → Bool
  | .edge x => x != 0 && decide (x < 64)
  | .coc i b h _ => decide (i < 3) && decide (b < 64) && decide (h < 64)
  | .diag q _ => q != 0 && decide (q < 64) && mulIdx q q == 0

def peel : ℕ → List Step → Bool
  | K, [] => K == 2 ^ 192 - 1
  | K, s :: l => s.valid && decide (s.pivot < 192) &&
      (s.mask ^^^ (s.mask &&& K) == 2 ^ s.pivot) && peel (K ||| 2 ^ s.pivot) l

def certSteps : List Step :=
  [.diag 1 1, .diag 2 66, .diag 3 131, .coc 0 1 2 6, .coc 0 1 3 8, .coc 0 1 4 10, .coc 0 1 5 12,
   .coc 0 1 7 16, .coc 0 1 9 20, .coc 0 1 11 24, .coc 0 1 13 28, .coc 0 1 15 31, .coc 0 1 17 35,
   .coc 0 1 18 37, .coc 0 1 19 39, .coc 0 1 23 43, .coc 0 1 25 47, .coc 0 1 26 49, .coc 0 1 27 51,
   .coc 0 14 2 86, .coc 1 2 1 68, .coc 1 2 3 73, .coc 1 2 5 77, .coc 1 2 6 78, .coc 1 2 7 81,
   .coc 1 2 8 82, .coc 1 2 11 89, .coc 1 2 12 90, .coc 1 2 15 96, .coc 1 2 16 97, .coc 1 2 20 104,
   .coc 1 2 23 108, .coc 1 2 24 109, .coc 1 2 28 116, .coc 1 21 3 164, .coc 1 37 3 170,
   .coc 1 58 3 188, .coc 2 3 1 133, .coc 2 3 2 135, .coc 2 3 4 139, .coc 2 3 6 143, .coc 2 3 8 147,
   .coc 2 3 9 149, .coc 2 3 10 151, .coc 2 3 12 155, .coc 2 3 13 157, .coc 2 3 14 158,
   .coc 2 3 16 162, .coc 2 3 18 166, .coc 2 3 20 169, .coc 2 3 24 174, .coc 2 3 25 176,
   .coc 2 3 26 178, .coc 2 3 28 181, .coc 2 3 31 182, .coc 2 3 32 183, .coc 2 3 33 184,
   .coc 2 3 35 185, .coc 2 3 37 186, .coc 2 3 43 187, .coc 2 3 45 189, .coc 2 3 47 190,
   .coc 2 3 49 191, .coc 2 39 8 52, .coc 2 40 42 42, .coc 2 51 5 40, .diag 22 22, .diag 29 29,
   .diag 34 98, .diag 36 100, .diag 44 44, .diag 45 45, .diag 46 46, .diag 50 50, .diag 53 53,
   .diag 54 118, .diag 59 59, .diag 63 63, .coc 0 1 14 14, .coc 0 1 21 21, .coc 0 1 30 30,
   .coc 0 1 32 32, .coc 0 1 33 33, .coc 0 1 34 34, .coc 0 1 38 38, .coc 0 1 41 41, .coc 0 1 54 54,
   .coc 0 1 58 58, .coc 0 14 3 101, .coc 0 14 5 113, .coc 0 14 7 99, .coc 0 14 9 106,
   .coc 0 14 11 111, .coc 0 14 13 94, .coc 0 14 15 95, .coc 0 14 23 107, .coc 0 21 2 36,
   .coc 0 21 3 83, .coc 0 21 4 48, .coc 0 21 5 91, .coc 0 21 6 55, .coc 0 21 10 60,
   .coc 0 21 11 110, .coc 0 21 15 167, .coc 0 21 17 121, .coc 0 21 27 179, .coc 0 21 34 56,
   .coc 0 21 38 180, .coc 0 21 41 168, .coc 0 21 42 115, .coc 0 21 43 123, .coc 0 21 46 61,
   .coc 0 21 52 103, .coc 0 21 54 62, .coc 0 21 57 57, .coc 0 30 13 117, .coc 0 30 17 114,
   .coc 0 30 26 127, .coc 0 30 33 124, .coc 0 30 35 93, .coc 0 30 44 120, .coc 0 32 3 105,
   .coc 0 32 7 125, .coc 0 32 8 122, .coc 0 32 11 126, .coc 0 32 12 85, .coc 0 32 16 119,
   .coc 0 32 30 102, .coc 0 32 31 112]

def allSteps : List Step := (List.range 63).map (fun k => Step.edge (k + 1)) ++ certSteps

theorem peel_allSteps : peel 0 allSteps = true := by decide +kernel

variable {g}

theorem peel_sound (hs : ∀ s : Step, s.valid = true → eval g s.mask = 0) :
    ∀ (l : List Step) (K : ℕ), (∀ k < 192, K.testBit k = true → val g k = 0) →
      peel K l = true → ∀ k < 192, val g k = 0
  | [], K, hK, hp, k, hk => by
    rw [peel, beq_iff_eq] at hp
    exact hK k hk (by rw [hp, Nat.testBit_two_pow_sub_one]; simpa using hk)
  | s :: l, K, hK, hp, k, hk => by
    simp only [peel, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    obtain ⟨⟨⟨hv, hj⟩, hm⟩, hp⟩ := hp
    refine peel_sound hs l _ (fun k' hk' hb => ?_) hp k hk
    rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at hb
    rcases hb with hb | rfl
    · exact hK k' hk' hb
    · have hsplit : s.mask = (s.mask &&& K) ^^^ (s.mask ^^^ (s.mask &&& K)) := by
        rw [← Nat.xor_assoc, Nat.xor_comm (s.mask &&& K) s.mask, Nat.xor_assoc, Nat.xor_self,
          Nat.xor_zero]
      have := hs s hv
      rw [hsplit, eval_xor, eval_and_eq_zero g hK, hm, eval_two_pow g hj, zero_add] at this
      exact this

variable (hl : ∀ b, g 1 b = 0) (hc : ∀ a b c, g a b + g (a * b) c = g b c + g a (b * c))
  (ht : ∀ x, x ≠ 0 → x < 64 → g (y (gen x)) (elt (par x)) = 0)
include hl hc ht

theorem eval_wmask : ∀ x, x < 64 → ∀ h, h < 64 → eval g (wmask x h) = g (elt x) (elt h) := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hx h hh
    by_cases hx0 : x = 0
    · subst hx0
      rw [wmask_zero, elt_zero, hl, eval, Finset.sum_eq_zero]
      intro k _
      simp
    · obtain ⟨hp, hg, -⟩ := tree_spec hx0 hx
      have hpx : par x < 64 := hp.trans hx
      obtain ⟨hm, hm'⟩ := mulIdx_spec hpx hh
      rw [wmask_cons hx0 hx, eval_xor, eval_two_pow g (by omega), val_eq g hm, hm',
        ih _ hp hpx h hh, elt_cons hx0 hx]
      have := hc (y (gen x)) (elt (par x)) (elt h)
      rw [ht x hx0 hx, zero_add] at this
      rw [this]
      grind

theorem eval_step_mask (hd : ∀ q : S, orderOf q = 2 → g q q = 0) (s : Step)
    (hv : s.valid = true) : eval g s.mask = 0 := by
  cases s with
  | edge x =>
    simp only [Step.valid, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hv
    obtain ⟨hx0, hx⟩ := hv
    obtain ⟨hp, hg, -⟩ := tree_spec hx0 hx
    rw [Step.mask, eval_two_pow g (by omega), val_eq g (by omega), ht x hx0 hx]
  | coc i b h j =>
    simp only [Step.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨hi, hb⟩, hh⟩ := hv
    obtain ⟨hl1, hl2⟩ := lmul_spec hi hb
    obtain ⟨hm1, hm2⟩ := mulIdx_spec hb hh
    rw [Step.mask, eval_xor, eval_xor, eval_xor, eval_two_pow g (by omega),
      eval_two_pow g (by omega), val_eq g hb, val_eq g hm1, eval_wmask hl hc ht _ hl1 h hh,
      eval_wmask hl hc ht _ hb h hh, hl2, hm2]
    have := hc (y i) (elt b) (elt h)
    grind
  | diag q j =>
    simp only [Step.valid, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq,
      beq_iff_eq] at hv
    obtain ⟨⟨hq0, hq⟩, hqq⟩ := hv
    rw [Step.mask, eval_wmask hl hc ht _ hq q hq]
    refine hd _ (orderOf_eq_prime ?_ fun h1 => hq0 ?_)
    · rw [pow_two, ← (mulIdx_spec hq hq).2, hqq, elt_zero]
    · exact elt_injective hq (by norm_num) (h1.trans elt_zero.symm)

theorem eq_zero_of_tree (hd : ∀ q : S, orderOf q = 2 → g q q = 0) (a b : S) : g a b = 0 := by
  have hval := peel_sound (eval_step_mask hl hc ht hd) allSteps 0 (by simp) peel_allSteps
  obtain ⟨x, hx, rfl⟩ := elt_surjective a
  obtain ⟨h, hh, rfl⟩ := elt_surjective b
  rw [← eval_wmask hl hc ht x hx h hh, eval_eq_zero g hval]

end Tree

theorem gen_par_succ {i : ℕ} (hi : i < 3) : gen (i + 1) = i ∧ par (i + 1) = 0 := by
  interval_cases i <;> decide +kernel

theorem elt_succ {i : ℕ} (hi : i < 3) : elt (i + 1) = y i := by
  rw [elt_cons (by omega) (by omega), (gen_par_succ hi).1, (gen_par_succ hi).2, elt_zero,
    mul_one]

end SylowTable

open SylowTable

theorem s₁_mem_M12 : s₁ ∈ NativeSporadic.M12 :=
  mem_M12_of_isCode isCode_s₁
    [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1,
     0, 1, 0]
    (by decide +kernel)

theorem s₂_mem_M12 : s₂ ∈ NativeSporadic.M12 :=
  mem_M12_of_isCode isCode_s₂
    [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1,
     1, 0, 1, 1, 0, 1, 0, 1, 0, 1]
    (by decide +kernel)

theorem s₃_mem_M12 : s₃ ∈ NativeSporadic.M12 :=
  mem_M12_of_isCode isCode_s₃
    [0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0,
     1, 0, 1, 0, 1, 0, 1, 0, 1, 0]
    (by decide +kernel)

theorem s₄_mem_M12 : s₄ ∈ NativeSporadic.M12 :=
  mem_M12_of_isCode isCode_s₄
    [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1,
     1, 0]
    (by decide +kernel)

theorem S_le_M12 : S ≤ NativeSporadic.M12 := by
  refine Subgroup.closure_le _ |>.2 ?_
  rintro σ (rfl | rfl | rfl | rfl)
  exacts [s₁_mem_M12, s₂_mem_M12, s₃_mem_M12, s₄_mem_M12]

theorem card_S : Nat.card S = 64 := by
  have hbij : Function.Bijective fun x : Fin 64 => elt x := by
    refine ⟨fun a b h => Fin.ext (elt_injective a.2 b.2 h), fun s => ?_⟩
    obtain ⟨x, hx, h⟩ := elt_surjective s
    exact ⟨⟨x, hx⟩, h⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem relIndex_S_M12 : S.relIndex NativeSporadic.M12 = 1485 := by
  have h := Subgroup.relIndex_mul_card S NativeSporadic.M12
  rw [inf_of_le_left S_le_M12, card_S, card_M12] at h
  omega

theorem card_subgroupOf_S : Nat.card (S.subgroupOf NativeSporadic.M12) = 64 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S_le_M12).toEquiv, card_S]

theorem factorization_card_M12 : (Nat.card NativeSporadic.M12).factorization 2 = 6 := by
  rw [card_M12, show (95040 : ℕ) = 2 ^ 6 * 1485 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬2 ∣ 1485)]
  rfl

noncomputable def sylow : Sylow 2 NativeSporadic.M12 :=
  Sylow.ofCard (S.subgroupOf NativeSporadic.M12) (by
    rw [card_subgroupOf_S, factorization_card_M12]
    norm_num)

theorem coe_sylow : (sylow : Subgroup NativeSporadic.M12) = S.subgroupOf NativeSporadic.M12 :=
  Sylow.coe_ofCard _ _

theorem exists_sylow_eq_S : ∃ P : Sylow 2 NativeSporadic.M12,
    (P : Subgroup NativeSporadic.M12) = S.subgroupOf NativeSporadic.M12 :=
  ⟨sylow, coe_sylow⟩

theorem exists_coboundary (f : S → S → ZMod 2) (hl : ∀ b, f 1 b = 0) (hr : ∀ a, f a 1 = 0)
    (hc : ∀ a b c, f a b + f (a * b) c = f b c + f a (b * c))
    (hd : ∀ q : S, orderOf q = 2 → f q q = 0) :
    ∃ μ : S → ZMod 2, ∀ a b, f a b = μ a + μ b + μ (a * b) := by
  let idx : S → ℕ := fun s => Classical.choose (elt_surjective s)
  have hidx : ∀ s, idx s < 64 ∧ elt (idx s) = s := fun s => Classical.choose_spec (elt_surjective s)
  have hidx_elt : ∀ x, x < 64 → idx (elt x) = x := fun x hx =>
    elt_injective (hidx _).1 hx (hidx _).2
  let lam : ℕ → ZMod 2 := fun x => ((path x).map fun z => f (y (gen z)) (elt (par z))).sum
  have lam_zero : lam 0 = 0 := by simp [lam, path_zero]
  have lam_cons : ∀ x, x ≠ 0 → x < 64 → lam x = f (y (gen x)) (elt (par x)) + lam (par x) :=
    fun x hx0 hx => by simp only [lam, path_cons hx0 hx, List.map_cons, List.sum_cons]
  let μ : S → ZMod 2 := fun s => lam (idx s)
  have μ_elt : ∀ x, x < 64 → μ (elt x) = lam x := fun x hx => by simp only [μ, hidx_elt x hx]
  have μ_one : μ 1 = 0 := by rw [← elt_zero, μ_elt 0 (by norm_num), lam_zero]
  refine ⟨μ, fun a b => ?_⟩
  have key := eq_zero_of_tree (g := fun a b => f a b + μ a + μ b + μ (a * b))
    (fun b => by simp [hl, μ_one, zmod_two_add_self])
    (fun a b c => by
      have := hc a b c
      rw [mul_assoc]
      grind)
    (fun x hx0 hx => by
      obtain ⟨hp, hg, -⟩ := tree_spec hx0 hx
      have hpx : par x < 64 := hp.trans hx
      have hy : μ (y (gen x)) = 0 := by
        rw [← elt_succ hg, μ_elt _ (by omega), lam_cons _ (by omega) (by omega),
          (gen_par_succ hg).1, (gen_par_succ hg).2, elt_zero, hr, lam_zero, add_zero]
      rw [← elt_cons hx0 hx, μ_elt x hx, μ_elt _ hpx, lam_cons x hx0 hx, hy]
      grind)
    (fun q hq => by
      have hqq : q * q = 1 := by rw [← pow_two, ← hq, pow_orderOf_eq_one]
      simp only [hqq, hd q hq, μ_one]
      grind) a b
  grind

end CFSG.ComponentClassification.M12Cover
