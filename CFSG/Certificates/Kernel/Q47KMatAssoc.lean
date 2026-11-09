module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Q47Tests
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Linarith

public section

namespace CFSG.KC.Q47K

open CFSG.ComponentClassification.AS81.Q47

theorem listSum_range47 (f : Nat → Nat) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, listSum_range47 f n, Finset.sum_range_succ]
    simp

theorem matMul_get47 {d p : Nat} (a b : List Nat) {e : Nat} (he : e < d * d) :
    (matMul d p a b)[e]! = (∑ k ∈ Finset.range d, a[e / d * d + k]! * b[k * d + e % d]!) % p := by
  unfold matMul
  rw [getElem!_pos _ e (by simpa using he), List.getElem_map, List.getElem_range, listSum_range47]

theorem matMul_length (d p : Nat) (a b : List Nat) : (matMul d p a b).length = d * d := by
  simp [matMul]

theorem matMul_assoc (d p : Nat) (a b c : List Nat) :
    matMul d p (matMul d p a b) c = matMul d p a (matMul d p b c) := by
  apply List.ext_getElem (by simp [matMul])
  intro e h1 h2
  have he : e < d * d := by simpa [matMul] using h1
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h
      simp at he
    · exact h
  rw [← getElem!_pos _ e h1, ← getElem!_pos _ e h2, matMul_get47 _ _ he, matMul_get47 _ _ he]
  have hq : e / d < d := (Nat.div_lt_iff_lt_mul hd).2 he
  have hr : e % d < d := Nat.mod_lt e hd
  have i1 : ∀ k < d, (e / d * d + k) < d * d := fun k hk => by nlinarith
  have i2 : ∀ k < d, (k * d + e % d) < d * d := fun k hk => by nlinarith
  have q1 : ∀ k < d, (e / d * d + k) / d = e / d ∧ (e / d * d + k) % d = k := fun k hk => by
    constructor
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hk, Nat.zero_add]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  have q2 : ∀ k < d, (k * d + e % d) / d = k ∧ (k * d + e % d) % d = e % d := fun k hk => by
    constructor
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hr, Nat.zero_add]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  have eL : (∑ k ∈ Finset.range d, (matMul d p a b)[e / d * d + k]! * (c)[k * d + e % d]!) % p =
      (∑ k ∈ Finset.range d, ∑ l ∈ Finset.range d,
        a[e / d * d + l]! * b[l * d + k]! * (c)[k * d + e % d]!) % p := by
    rw [Finset.sum_nat_mod]
    conv_rhs => rw [Finset.sum_nat_mod]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    rw [matMul_get47 _ _ (i1 k hk'), (q1 k hk').1, (q1 k hk').2, Nat.mod_mul_mod, Finset.sum_mul]
  have eR : (∑ l ∈ Finset.range d, a[e / d * d + l]! * (matMul d p b c)[l * d + e % d]!) % p =
      (∑ k ∈ Finset.range d, ∑ l ∈ Finset.range d,
        a[e / d * d + l]! * b[l * d + k]! * (c)[k * d + e % d]!) % p := by
    conv_rhs => rw [Finset.sum_comm, Finset.sum_nat_mod]
    rw [Finset.sum_nat_mod]
    congr 1
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' := Finset.mem_range.1 hl
    rw [matMul_get47 _ _ (i2 l hl'), (q2 l hl').1, (q2 l hl').2, Nat.mul_mod_mod, Finset.mul_sum]
    simp only [Nat.mul_assoc]
  rw [eL, eR]

theorem getElem!_map0 {f : Nat → Nat} (hf : f 0 = 0) (a : List Nat) (i : Nat) :
    (a.map f)[i]! = f a[i]! := by
  by_cases h : i < a.length
  · rw [getElem!_pos _ i (by simpa using h), getElem!_pos a i h, List.getElem_map]
  · rw [getElem!_neg _ i (by simpa using h), getElem!_neg a i h]
    exact hf.symm

theorem matMul_map_right (d : Nat) (c a : List Nat) (l : Nat) :
    matMul d 7 c (a.map (· * l % 7)) = (matMul d 7 c a).map (· * l % 7) := by
  apply List.ext_getElem (by simp [matMul])
  intro e h1 h2
  have he : e < d * d := by simpa [matMul] using h1
  rw [← getElem!_pos _ e h1, ← getElem!_pos _ e h2, getElem!_map0 (by simp), matMul_get47 _ _ he,
    matMul_get47 _ _ he]
  simp only [getElem!_map0 (f := (· * l % 7)) (by simp)]
  conv_lhs => rw [Finset.sum_nat_mod]
  conv_rhs => rw [Nat.mod_mul_mod, Finset.sum_mul, Finset.sum_nat_mod]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.mul_mod_mod, Nat.mul_assoc]

theorem matMul_map_left (d : Nat) (a c : List Nat) (l : Nat) :
    matMul d 7 (a.map (· * l % 7)) c = (matMul d 7 a c).map (· * l % 7) := by
  apply List.ext_getElem (by simp [matMul])
  intro e h1 h2
  have he : e < d * d := by simpa [matMul] using h1
  rw [← getElem!_pos _ e h1, ← getElem!_pos _ e h2, getElem!_map0 (by simp), matMul_get47 _ _ he,
    matMul_get47 _ _ he]
  simp only [getElem!_map0 (f := (· * l % 7)) (by simp)]
  conv_lhs => rw [Finset.sum_nat_mod]
  conv_rhs => rw [Nat.mod_mul_mod, Finset.sum_mul, Finset.sum_nat_mod]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.mod_mul_mod, Nat.mul_right_comm]

theorem projEq7_iff (a b : List Nat) :
    projEq7 b a = true ↔ ∃ l < 7, l ≠ 0 ∧ b = a.map (· * l % 7) := by
  simp only [projEq7, List.any_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq]

theorem projEq7_symm {a b : List Nat} (ha : ∀ x ∈ a, x < 7) (h : projEq7 b a = true) :
    projEq7 a b = true := by
  obtain ⟨l, hl, hl0, rfl⟩ := (projEq7_iff a b).1 h
  have inv : ∀ l < 7, l ≠ 0 → ∃ l' < 7, l' ≠ 0 ∧ ∀ x < 7, x * l % 7 * l' % 7 = x := by decide
  obtain ⟨l', hl', hl0', hx⟩ := inv l hl hl0
  refine (projEq7_iff _ _).2 ⟨l', hl', hl0', ?_⟩
  rw [List.map_map]
  conv_lhs => rw [← List.map_id a]
  exact List.map_congr_left fun x hx' => (hx x (ha x hx')).symm

theorem projEq7_trans {a b c : List Nat} (h1 : projEq7 b a = true) (h2 : projEq7 c b = true) :
    projEq7 c a = true := by
  obtain ⟨l1, hl1, hl10, rfl⟩ := (projEq7_iff a b).1 h1
  obtain ⟨l2, hl2, hl20, rfl⟩ := (projEq7_iff _ c).1 h2
  have nz : ∀ l1 < 7, ∀ l2 < 7, l1 ≠ 0 → l2 ≠ 0 → l1 * l2 % 7 ≠ 0 := by decide
  refine (projEq7_iff _ _).2 ⟨l1 * l2 % 7, Nat.mod_lt _ (by decide), nz l1 hl1 l2 hl2 hl10 hl20, ?_⟩
  rw [List.map_map]
  refine List.map_congr_left fun x _ => ?_
  change x * l1 % 7 * l2 % 7 = x * (l1 * l2 % 7) % 7
  rw [Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mul_assoc]

theorem projEq7_left {a b : List Nat} (c : List Nat) (h : projEq7 b a = true) :
    projEq7 (matMul 2 7 c b) (matMul 2 7 c a) = true := by
  obtain ⟨l, hl, hl0, rfl⟩ := (projEq7_iff a b).1 h
  exact (projEq7_iff _ _).2 ⟨l, hl, hl0, matMul_map_right 2 c a l⟩

theorem projEq7_right {a b : List Nat} (c : List Nat) (h : projEq7 b a = true) :
    projEq7 (matMul 2 7 b c) (matMul 2 7 a c) = true := by
  obtain ⟨l, hl, hl0, rfl⟩ := (projEq7_iff a b).1 h
  exact (projEq7_iff _ _).2 ⟨l, hl, hl0, matMul_map_left 2 a c l⟩

theorem matMul_lt (d p : Nat) (hp : 0 < p) (a b : List Nat) : ∀ x ∈ matMul d p a b, x < p := by
  intro x hx
  unfold matMul at hx
  obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
  exact Nat.mod_lt _ hp

end CFSG.KC.Q47K

end
