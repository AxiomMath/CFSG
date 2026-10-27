module

public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Heis

@[expose] def add4 (a b : Fin 4) : Fin 4 :=
  ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]] a b

@[expose] def mul4 (a b : Fin 4) : Fin 4 :=
  ![![0, 0, 0, 0], ![0, 1, 2, 3], ![0, 2, 3, 1], ![0, 3, 1, 2]] a b

abbrev M3 : Type := Fin 3 → Fin 3 → Fin 4

@[expose] def mmul (A B : M3) : M3 := fun i k =>
  add4 (add4 (mul4 (A i 0) (B 0 k)) (mul4 (A i 1) (B 1 k))) (mul4 (A i 2) (B 2 k))

@[expose] def madd (A B : M3) : M3 := fun i k => add4 (A i k) (B i k)

@[expose] def msmul (c : Fin 4) (A : M3) : M3 := fun i k => mul4 c (A i k)

@[expose] def mone : M3 := ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]

@[expose] def mdet (A : M3) : Fin 4 :=
  add4 (add4 (add4 (mul4 (A 0 0) (mul4 (A 1 1) (A 2 2))) (mul4 (A 0 0) (mul4 (A 1 2) (A 2 1))))
    (add4 (mul4 (A 0 1) (mul4 (A 1 0) (A 2 2))) (mul4 (A 0 1) (mul4 (A 1 2) (A 2 0)))))
    (add4 (mul4 (A 0 2) (mul4 (A 1 0) (A 2 1))) (mul4 (A 0 2) (mul4 (A 1 1) (A 2 0))))

@[expose] def mpow (A : M3) : ℕ → M3
  | 0 => mone
  | n + 1 => mmul (mpow A n) A

@[expose] def dM (z : Fin 4) : M3 := ![![1, 0, 0], ![0, z, 0], ![0, 0, mul4 z z]]

@[expose] def CM (m : Fin 4) : M3 := ![![0, 0, m], ![1, 0, 0], ![0, 1, 0]]

@[expose] def uM (z m : Fin 4) : Fin 2 → M3
  | 0 => CM m
  | 1 => mmul (CM m) (dM z)

@[expose] def yM (z m : Fin 4) (i : Fin 2) : M3 :=
  madd (uM z m i) (msmul (mul4 m m) (mmul (uM z m i) (uM z m i)))

@[expose] def tvM (i j : Fin 3) (a : Fin 4) : M3 := fun r c =>
  if r = c then 1 else if r = i ∧ c = j then a else 0

@[expose] def meq (A B : M3) : Bool :=
  (List.finRange 3).all fun i => (List.finRange 3).all fun j => decide (A i j = B i j)

theorem meq_iff {A B : M3} : meq A B = true ↔ A = B := by
  simp [meq, List.all_eq_true, funext_iff]

@[expose] def evalW (A B : M3) (w : List Bool) : M3 :=
  w.foldl (fun acc b => mmul acc (if b then B else A)) mone

@[expose] def GoodPar (z m : Fin 4) : Prop := (z = 2 ∨ z = 3) ∧ (m = 2 ∨ m = 3)

instance (z m : Fin 4) : Decidable (GoodPar z m) := by unfold GoodPar; infer_instance

@[expose] def wordTab : List (Fin 4 × Fin 4 × Fin 3 × Fin 3 × Fin 4 × List Bool) := [
  (2, 2, 0, 1, 1, [true, false, false, false, false, true, false, true, true, true, true, false]),
  (2, 2, 0, 1, 2, [true, true, false, true, true, false, false, true, false, false]),
  (2, 2, 0, 1, 3, [false, true, false, true, false, true, true, false, false, true, true, true, true, false, true, false]),
  (2, 2, 0, 2, 1, [false, false, true, true, true, true, false, false, true, false, true]),
  (2, 2, 0, 2, 2, [false, true, true, false, true, false, false, false, true, true, true, true, false, false, false, true]),
  (2, 2, 0, 2, 3, [false, false, false, false, true, false, false, false, false, true, true, false, false, true, true]),
  (2, 2, 1, 0, 1, [false, true, true, true, true, false, true, false, false, false, false, true]),
  (2, 2, 1, 0, 2, [false, true, false, true, true, true, true, false, false, true, true, false, true, false, true, false]),
  (2, 2, 1, 0, 3, [false, false, true, false, false, true, true, false, true, true]),
  (2, 2, 1, 2, 1, [true, true, false, false, false, false, true, true, false, true, false]),
  (2, 2, 1, 2, 2, [true, true, true, true, false, true, true, true, true, false, false, true, true, false, false]),
  (2, 2, 1, 2, 3, [true, false, false, true, false, false, false, false, true, true, true, true, false, false, false, false]),
  (2, 2, 2, 0, 1, [true, false, true, false, false, true, true, true, true, false, false]),
  (2, 2, 2, 0, 2, [true, true, false, false, true, true, false, false, false, false, true, false, false, false, false]),
  (2, 2, 2, 0, 3, [true, false, false, false, true, true, true, true, false, false, false, true, false, true, true, false]),
  (2, 2, 2, 1, 1, [false, true, false, true, true, false, false, false, false, true, true]),
  (2, 2, 2, 1, 2, [false, false, false, false, true, true, true, true, false, false, false, false, true, false, false, true]),
  (2, 2, 2, 1, 3, [false, false, true, true, false, false, true, true, true, true, false, true, true, true, true]),
  (2, 3, 0, 1, 1, [false, true, true, true, true, false, true, false, false, false, false, true]),
  (2, 3, 0, 1, 2, [false, true, false, true, true, true, true, false, false, true, true, false, true, false, true, false]),
  (2, 3, 0, 1, 3, [false, false, true, false, false, true, true, false, true, true]),
  (2, 3, 0, 2, 1, [true, true, true, true, false, true, true, true, true, false, false, true, true, false, false]),
  (2, 3, 0, 2, 2, [true, false, false, true, false, false, false, false, true, true, true, true, false, false, false, false]),
  (2, 3, 0, 2, 3, [true, true, false, false, false, false, true, true, false, true, false]),
  (2, 3, 1, 0, 1, [true, false, false, false, false, true, false, true, true, true, true, false]),
  (2, 3, 1, 0, 2, [true, true, false, true, true, false, false, true, false, false]),
  (2, 3, 1, 0, 3, [false, true, false, true, false, true, true, false, false, true, true, true, true, false, true, false]),
  (2, 3, 1, 2, 1, [false, true, true, false, true, false, false, false, true, true, true, true, false, false, false, true]),
  (2, 3, 1, 2, 2, [false, false, false, false, true, false, false, false, false, true, true, false, false, true, true]),
  (2, 3, 1, 2, 3, [false, false, true, true, true, true, false, false, true, false, true]),
  (2, 3, 2, 0, 1, [false, false, true, true, false, false, true, true, true, true, false, true, true, true, true]),
  (2, 3, 2, 0, 2, [false, true, false, true, true, false, false, false, false, true, true]),
  (2, 3, 2, 0, 3, [false, false, false, false, true, true, true, true, false, false, false, false, true, false, false, true]),
  (2, 3, 2, 1, 1, [true, false, false, false, true, true, true, true, false, false, false, true, false, true, true, false]),
  (2, 3, 2, 1, 2, [true, false, true, false, false, true, true, true, true, false, false]),
  (2, 3, 2, 1, 3, [true, true, false, false, true, true, false, false, false, false, true, false, false, false, false]),
  (3, 2, 0, 1, 1, [false, true, true, true, true, false, true, false, false, false, false, true]),
  (3, 2, 0, 1, 2, [false, false, true, false, false, true, true, false, true, true]),
  (3, 2, 0, 1, 3, [false, true, false, true, true, true, true, false, false, true, true, false, true, false, true, false]),
  (3, 2, 0, 2, 1, [true, true, true, true, false, true, true, true, true, false, false, true, true, false, false]),
  (3, 2, 0, 2, 2, [true, true, false, false, false, false, true, true, false, true, false]),
  (3, 2, 0, 2, 3, [true, false, false, true, false, false, false, false, true, true, true, true, false, false, false, false]),
  (3, 2, 1, 0, 1, [true, false, false, false, false, true, false, true, true, true, true, false]),
  (3, 2, 1, 0, 2, [false, true, false, true, false, true, true, false, false, true, true, true, true, false, true, false]),
  (3, 2, 1, 0, 3, [true, true, false, true, true, false, false, true, false, false]),
  (3, 2, 1, 2, 1, [false, true, true, false, true, false, false, false, true, true, true, true, false, false, false, true]),
  (3, 2, 1, 2, 2, [false, false, true, true, true, true, false, false, true, false, true]),
  (3, 2, 1, 2, 3, [false, false, false, false, true, false, false, false, false, true, true, false, false, true, true]),
  (3, 2, 2, 0, 1, [false, false, true, true, false, false, true, true, true, true, false, true, true, true, true]),
  (3, 2, 2, 0, 2, [false, false, false, false, true, true, true, true, false, false, false, false, true, false, false, true]),
  (3, 2, 2, 0, 3, [false, true, false, true, true, false, false, false, false, true, true]),
  (3, 2, 2, 1, 1, [true, false, false, false, true, true, true, true, false, false, false, true, false, true, true, false]),
  (3, 2, 2, 1, 2, [true, true, false, false, true, true, false, false, false, false, true, false, false, false, false]),
  (3, 2, 2, 1, 3, [true, false, true, false, false, true, true, true, true, false, false]),
  (3, 3, 0, 1, 1, [true, false, false, false, false, true, false, true, true, true, true, false]),
  (3, 3, 0, 1, 2, [false, true, false, true, false, true, true, false, false, true, true, true, true, false, true, false]),
  (3, 3, 0, 1, 3, [true, true, false, true, true, false, false, true, false, false]),
  (3, 3, 0, 2, 1, [false, false, true, true, true, true, false, false, true, false, true]),
  (3, 3, 0, 2, 2, [false, false, false, false, true, false, false, false, false, true, true, false, false, true, true]),
  (3, 3, 0, 2, 3, [false, true, true, false, true, false, false, false, true, true, true, true, false, false, false, true]),
  (3, 3, 1, 0, 1, [false, true, true, true, true, false, true, false, false, false, false, true]),
  (3, 3, 1, 0, 2, [false, false, true, false, false, true, true, false, true, true]),
  (3, 3, 1, 0, 3, [false, true, false, true, true, true, true, false, false, true, true, false, true, false, true, false]),
  (3, 3, 1, 2, 1, [true, true, false, false, false, false, true, true, false, true, false]),
  (3, 3, 1, 2, 2, [true, false, false, true, false, false, false, false, true, true, true, true, false, false, false, false]),
  (3, 3, 1, 2, 3, [true, true, true, true, false, true, true, true, true, false, false, true, true, false, false]),
  (3, 3, 2, 0, 1, [true, false, true, false, false, true, true, true, true, false, false]),
  (3, 3, 2, 0, 2, [true, false, false, false, true, true, true, true, false, false, false, true, false, true, true, false]),
  (3, 3, 2, 0, 3, [true, true, false, false, true, true, false, false, false, false, true, false, false, false, false]),
  (3, 3, 2, 1, 1, [false, true, false, true, true, false, false, false, false, true, true]),
  (3, 3, 2, 1, 2, [false, false, true, true, false, false, true, true, true, true, false, true, true, true, true]),
  (3, 3, 2, 1, 3, [false, false, false, false, true, true, true, true, false, false, false, false, true, false, false, true])
]

@[expose] def wordsOK : Bool :=
  wordTab.all fun t => meq (evalW (yM t.1 t.2.1 0) (yM t.1 t.2.1 1) t.2.2.2.2.2)
    (tvM t.2.2.1 t.2.2.2.1 t.2.2.2.2.1)

@[expose] def wordsCover : Bool :=
  (List.finRange 4).all fun z => (List.finRange 4).all fun m =>
    (List.finRange 3).all fun i => (List.finRange 3).all fun j => (List.finRange 4).all fun a =>
      decide (¬ GoodPar z m ∨ i = j ∨ a = 0 ∨
        ∃ t ∈ wordTab, t.1 = z ∧ t.2.1 = m ∧ t.2.2.1 = i ∧ t.2.2.2.1 = j ∧ t.2.2.2.2.1 = a)

theorem words_ok : wordsOK = true := by decide +kernel

theorem words_cover : wordsCover = true := by decide +kernel

theorem yM_det : ∀ z m : Fin 4, GoodPar z m → ∀ i : Fin 2, mdet (yM z m i) = 1 := by decide +kernel

theorem yM_pow7 : ∀ z m : Fin 4, GoodPar z m → ∀ i : Fin 2, meq (mpow (yM z m i) 7) mone = true := by
  decide +kernel

theorem yM_comm : ∀ z m : Fin 4, GoodPar z m → ∀ i : Fin 2,
    meq (mmul (uM z m i) (yM z m i)) (mmul (yM z m i) (uM z m i)) = true := by decide +kernel

theorem uM_entry : ∀ z m : Fin 4, ∀ i : Fin 2, uM z m i 1 0 = 1 := by decide +kernel

theorem exists_word (z m : Fin 4) (hg : GoodPar z m) (i j : Fin 3) (hij : i ≠ j) (a : Fin 4) :
    ∃ w : List Bool, evalW (yM z m 0) (yM z m 1) w = tvM i j a := by
  by_cases ha : a = 0
  · refine ⟨[], ?_⟩
    subst ha
    funext r c
    fin_cases r <;> fin_cases c <;> simp [evalW, mone, tvM]
  · have hcov := words_cover
    simp only [wordsCover, List.all_eq_true, List.mem_finRange, true_implies,
      decide_eq_true_eq] at hcov
    obtain ⟨t, ht, hz, hm, hi, hj, hc⟩ :=
      ((hcov z m i j a).resolve_left (not_not.2 hg)).resolve_left hij |>.resolve_left ha
    have hok := words_ok
    simp only [wordsOK, List.all_eq_true] at hok
    have h1 := meq_iff.1 (hok t ht)
    obtain ⟨z', m', i', j', a', w⟩ := t
    simp only at hz hm hi hj hc
    subst hz hm hi hj hc
    exact ⟨w, h1⟩

end CFSG.HardMathSupport.Dickson.Sec6.Heis
