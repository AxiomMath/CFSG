module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Finset.Card

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus.KacMask

@[expose] def code {r : ℕ} : Option (Fin r) → ℕ
  | none => r
  | some j => j

theorem code_lt {r : ℕ} (x : Option (Fin r)) : code x < r + 1 := by
  cases x with
  | none => exact Nat.lt_succ_self r
  | some j => exact Nat.lt_succ_of_lt j.isLt

theorem code_injective {r : ℕ} : Function.Injective (code (r := r)) := by
  intro x y h
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some j => exact absurd h (by simp [code]; omega)
  | some i =>
    cases y with
    | none => exact absurd h (by simp [code]; omega)
    | some j => simp only [code] at h; rw [Fin.ext h]

@[expose] def setOf (r m : ℕ) : Finset (Option (Fin r)) :=
  Finset.univ.filter fun x => m.testBit (code x)

theorem mem_setOf {r m : ℕ} {x : Option (Fin r)} : x ∈ setOf r m ↔ m.testBit (code x) = true := by
  simp [setOf]

theorem exists_setOf {r : ℕ} (C : Finset (Option (Fin r))) : ∃ m < 2 ^ (r + 1), setOf r m = C := by
  classical
  induction C using Finset.induction_on with
  | empty => exact ⟨0, Nat.two_pow_pos _, by ext x; simp [mem_setOf]⟩
  | insert a C ha ih =>
    obtain ⟨m, hm, rfl⟩ := ih
    refine ⟨m ||| 2 ^ code a,
      Nat.or_lt_two_pow hm (Nat.pow_lt_pow_right (by decide) (code_lt a)), ?_⟩
    ext x
    simp only [mem_setOf, Finset.mem_insert, Nat.testBit_or, Nat.testBit_two_pow,
      Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl (code_injective h).symm
    · rintro (rfl | h)
      · exact Or.inr rfl
      · exact Or.inl h

theorem forall_finset {r : ℕ} {P : Finset (Option (Fin r)) → Prop}
    (h : ∀ m < 2 ^ (r + 1), P (setOf r m)) : ∀ C, P C := by
  intro C
  obtain ⟨m, hm, rfl⟩ := exists_setOf C
  exact h m hm

@[expose] def bitsOf (n : ℕ) (p : ℕ → Bool) : ℕ :=
  (List.range n).foldl (fun acc j => if p j then acc ||| 2 ^ j else acc) 0

theorem testBit_bitsOf (n : ℕ) (p : ℕ → Bool) (j : ℕ) :
    (bitsOf n p).testBit j = (decide (j < n) && p j) := by
  have key : ∀ (l : List ℕ) (acc : ℕ), (l.foldl (fun acc j => if p j then acc ||| 2 ^ j else acc)
      acc).testBit j = (acc.testBit j || (decide (j ∈ l) && p j)) := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons a l ih =>
      intro acc
      rw [List.foldl_cons, ih]
      by_cases hpa : p a = true
      · simp only [hpa, ite_true, Nat.testBit_or, Nat.testBit_two_pow, List.mem_cons]
        by_cases hja : a = j
        · subst hja; simp [hpa]
        · have : ¬ j = a := fun h => hja h.symm
          simp [hja, this]
      · have hpa' : p a = false := by simpa using hpa
        simp only [hpa', Bool.false_eq_true, ite_false, List.mem_cons]
        by_cases hja : j = a
        · subst hja; simp [hpa']
        · simp [hja]
  rw [bitsOf, key, Nat.zero_testBit, Bool.false_or]
  simp [List.mem_range]

@[expose] def zm {r : ℕ} (v : Fin r → ℤ) : ℕ :=
  bitsOf r fun i => if h : i < r then decide (v ⟨i, h⟩ ≠ 0) else false

theorem forall_zero_iff {r : ℕ} (v : Fin r → ℤ) (m : ℕ) :
    (∀ j : Fin r, m.testBit j = false → v j = 0) ↔ (zm v &&& m == zm v) = true := by
  rw [beq_iff_eq]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, zm, testBit_bitsOf]
    by_cases hi : i < r
    · simp only [hi, decide_true, dite_true, Bool.true_and]
      by_cases hm : m.testBit i = true
      · simp [hm]
      · have := h ⟨i, hi⟩ (by simpa using hm)
        simp [this]
    · simp [hi]
  · intro h j hj
    have := congrArg (fun n => n.testBit j) h
    simp only [Nat.testBit_and, zm, testBit_bitsOf, j.isLt, decide_true, dite_true,
      Bool.true_and, Fin.eta, hj, Bool.and_false] at this
    by_contra hne
    simp [hne] at this


@[expose] def kacTestB (r m z a b : ℕ) : Bool :=
  (z &&& m == z) || (m.testBit r && ((a &&& m == a) || (b &&& m == b)))

theorem not_mem_setOf_some {r m : ℕ} (j : Fin r) : some j ∉ setOf r m ↔ m.testBit j = false := by
  rw [mem_setOf]; simp [code]

theorem mem_setOf_none {r m : ℕ} : (none : Option (Fin r)) ∈ setOf r m ↔ m.testBit r = true := by
  rw [mem_setOf]; rfl

end CFSG.HardMathSupport.Timmesfeld.LangTorus.KacMask
