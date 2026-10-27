module

public import CFSG.Certificates.Kernel.LocalQTCoreCSnd.EltDef
import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.List.GetD

public section

namespace CFSG.KC.LQT.Syl.CoreSnd

variable {G : Type*} [Group G]

theorem elt_zero (k : ℕ) (B : List G) : elt k B 0 = 1 := by
  have hf : (fun (acc : G) (i : ℕ) => if (0 : ℕ).testBit i then acc * B.getD i 1 else acc)
      = fun acc _ => acc := by
    funext acc i
    simp [Nat.zero_testBit]
  have key : ∀ (l : List ℕ) (a : G), l.foldl (fun acc (_ : ℕ) => acc) a = a := by
    intro l
    induction l with
    | nil => intro a; rfl
    | cons x xs ih => intro a; simp only [List.foldl_cons]; exact ih a
  unfold elt
  rw [hf]
  exact key _ 1

theorem elt_succ (k : ℕ) (B : List G) (m : ℕ) :
    elt (k + 1) B m = elt k B m * (if m.testBit k then B.getD k 1 else 1) := by
  unfold elt
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  by_cases h : m.testBit k <;> simp [h]

private theorem kpw_getD_mem_closure (B : List G) (k : ℕ) :
    B.getD k 1 ∈ Subgroup.closure {b | b ∈ B} := by
  by_cases hk : k < B.length
  · rw [List.getD_eq_getElem _ _ hk]
    have hmem : B[k] ∈ {b : G | b ∈ B} := List.getElem_mem hk
    exact Subgroup.subset_closure hmem
  · rw [List.getD_eq_default _ _ (show B.length ≤ k by omega)]
    exact Subgroup.one_mem _

theorem elt_mem_closure (B : List G) (k m : ℕ) : elt k B m ∈ Subgroup.closure {b | b ∈ B} := by
  induction k with
  | zero =>
    simp only [elt, List.range_zero, List.foldl_nil]
    exact Subgroup.one_mem _
  | succ k ih =>
    rw [elt_succ]
    refine Subgroup.mul_mem _ ih ?_
    split_ifs
    · exact kpw_getD_mem_closure B k
    · exact Subgroup.one_mem _

theorem EFacts.sq' {B : List G} (h : EFacts B) (i : ℕ) : B.getD i 1 * B.getD i 1 = 1 := by
  by_cases hi : i < B.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h.sq _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (show B.length ≤ i by omega)]
    simp

theorem EFacts.comm' {B : List G} (h : EFacts B) (i j : ℕ) :
    B.getD i 1 * B.getD j 1 = B.getD j 1 * B.getD i 1 := by
  by_cases hi : i < B.length <;> by_cases hj : j < B.length
  · rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
    exact h.comm _ (List.getElem_mem hi) _ (List.getElem_mem hj)
  · rw [List.getD_eq_getElem _ _ hi, List.getD_eq_default _ _ (show B.length ≤ j by omega)]
    simp
  · rw [List.getD_eq_default _ _ (show B.length ≤ i by omega), List.getD_eq_getElem _ _ hj]
    simp
  · rw [List.getD_eq_default _ _ (show B.length ≤ i by omega),
      List.getD_eq_default _ _ (show B.length ≤ j by omega)]

theorem elt_comm {B : List G} (hc : ∀ i j, B.getD i 1 * B.getD j 1 = B.getD j 1 * B.getD i 1)
    (i k m : ℕ) : B.getD i 1 * elt k B m = elt k B m * B.getD i 1 := by
  induction k with
  | zero => simp [elt]
  | succ k ih =>
    rw [elt_succ]
    by_cases hb : m.testBit k
    · rw [if_pos hb, ← mul_assoc, ih, mul_assoc, hc i k, ← mul_assoc]
    · rw [if_neg hb, mul_one, ih]

private theorem kpw_xor_step (a a' b : G) (hs : b * b = 1) (hc : b * a' = a' * b) (s t : Bool) :
    a * (if s = true then b else 1) * (a' * (if t = true then b else 1)) =
      a * a' * (if (s ^^ t) = true then b else 1) := by
  have key : b * (a' * b) = a' := by
    rw [← mul_assoc, hc, mul_assoc, hs, mul_one]
  cases s <;> cases t <;> simp [mul_assoc, hc, key]

theorem elt_mul {B : List G} (hs : ∀ i, B.getD i 1 * B.getD i 1 = 1)
    (hc : ∀ i j, B.getD i 1 * B.getD j 1 = B.getD j 1 * B.getD i 1) (k m m' : ℕ) :
    elt k B m * elt k B m' = elt k B (m ^^^ m') := by
  induction k with
  | zero => simp [elt]
  | succ k ih =>
    rw [elt_succ, elt_succ, elt_succ, Nat.testBit_xor, ← ih]
    exact kpw_xor_step _ _ _ (hs k) (elt_comm hc k k m') _ _

private theorem kpw_elt_one (B : List G) {k m : ℕ} (h : ∀ j < k, m.testBit j = false) :
    elt k B m = 1 := by
  induction k with
  | zero => simp [elt]
  | succ k ih =>
    have hk : ¬ m.testBit k = true := by
      rw [h k (by omega)]
      decide
    rw [elt_succ, ih (fun j hj => h j (by omega)), if_neg hk, mul_one]

theorem elt_pow (B : List G) {i k : ℕ} (hi : i < k) : elt k B (2 ^ i) = B.getD i 1 := by
  induction k generalizing i with
  | zero => exact absurd hi (Nat.not_lt_zero i)
  | succ k ih =>
    rw [elt_succ]
    rcases Nat.lt_or_ge i k with hlt | hge
    · have hb : ¬ (2 ^ i).testBit k = true := by
        rw [Nat.testBit_two_pow, decide_eq_true_eq]
        omega
      rw [ih hlt, if_neg hb, mul_one]
    · have hieq : i = k := by omega
      have hb : (2 ^ i).testBit k = true := by
        rw [Nat.testBit_two_pow, hieq]
        simp
      have h1 : elt k B (2 ^ i) = 1 := by
        apply kpw_elt_one
        intro j hj
        rw [Nat.testBit_two_pow, decide_eq_false_iff_not]
        omega
      rw [h1, if_pos hb, one_mul, hieq]

theorem lst_length (B : List G) : (lst B).length = 16 := by
  simp [lst]

theorem mem_lst_iff {B : List G} {x : G} : x ∈ lst B ↔ ∃ m < 16, elt 4 B m = x := by
  simp [lst, List.mem_map, List.mem_range]

theorem one_mem_lst (B : List G) : (1 : G) ∈ lst B := by
  rw [mem_lst_iff]
  exact ⟨0, by omega, elt_zero 4 B⟩

theorem lst_mul {B : List G} (h : EFacts B) {x y : G} (hx : x ∈ lst B) (hy : y ∈ lst B) :
    x * y ∈ lst B := by
  obtain ⟨m, hm, rfl⟩ := mem_lst_iff.mp hx
  obtain ⟨m', hm', rfl⟩ := mem_lst_iff.mp hy
  have hlt : m ^^^ m' < 16 := Nat.xor_lt_two_pow (n := 4) hm hm'
  rw [elt_mul h.sq' h.comm' 4 m m']
  exact mem_lst_iff.mpr ⟨m ^^^ m', hlt, rfl⟩

theorem mem_lst_of_mem {B : List G} (h : EFacts B) {b : G} (hb : b ∈ B) : b ∈ lst B := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
  have hl : i < 4 := by
    have := h.len
    omega
  have h16 : (2 : ℕ) ^ i < 16 := by
    calc (2 : ℕ) ^ i < 2 ^ 4 := Nat.pow_lt_pow_right (by decide) hl
      _ = 16 := by decide
  refine mem_lst_iff.mpr ⟨2 ^ i, h16, ?_⟩
  rw [elt_pow B hl, List.getD_eq_getElem _ _ hi]

private theorem kpw_elt_zero_left (B : List G) (m : ℕ) : elt 0 B m = 1 := by
  simp [elt]

private theorem kpw_elt_eq_filter (B : List G) (m k : ℕ) :
    elt k B m = (((List.range k).filter (fun i => m.testBit i)).map (fun i => B.getD i 1)).prod := by
  induction k with
  | zero => simp [kpw_elt_zero_left]
  | succ k ih =>
    rw [elt_succ, ih, List.range_succ, List.filter_append, List.map_append, List.prod_append]
    by_cases hk : m.testBit k <;> simp [hk]

theorem mem_closure_iff_lst {B : List G} (h : EFacts B) (x : G) :
    x ∈ Subgroup.closure {b | b ∈ B} ↔ x ∈ lst B := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction_right with
    | one => exact one_mem_lst B
    | mul_right x _ y hy ih =>
      have hy' : y ∈ B := hy
      exact lst_mul h ih (mem_lst_of_mem h hy')
    | mul_inv_cancel x _ y hy ih =>
      have hy' : y ∈ B := hy
      rw [inv_eq_of_mul_eq_one_right (h.sq y hy')]
      exact lst_mul h ih (mem_lst_of_mem h hy')
  · intro hx
    obtain ⟨m, _, rfl⟩ := mem_lst_iff.1 hx
    exact elt_mem_closure B 4 m

theorem exists_word_lst {B : List G} (h : EFacts B) {x : G} (hx : x ∈ lst B) :
    ∃ l : List G, (∀ g ∈ l, g ∈ B) ∧ l.length ≤ 4 ∧ l.prod = x := by
  obtain ⟨m, _, rfl⟩ := mem_lst_iff.1 hx
  refine ⟨((List.range 4).filter (fun i => m.testBit i)).map (fun i => B.getD i 1), ?_, ?_,
    (kpw_elt_eq_filter B m 4).symm⟩
  · intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
    show B.getD i 1 ∈ B
    have hi4 : i < 4 := List.mem_range.1 (List.mem_filter.1 hi).1
    have hiB : i < B.length := by rw [h.len]; exact hi4
    rw [List.getD_eq_getElem _ _ hiB]
    exact List.getElem_mem hiB
  · simp only [List.length_map]
    exact (List.length_filter_le _ _).trans (by simp)

end CFSG.KC.LQT.Syl.CoreSnd

end
