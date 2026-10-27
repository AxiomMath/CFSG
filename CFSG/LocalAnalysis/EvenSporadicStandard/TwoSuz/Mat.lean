module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.EvenSporadicStandard.TwoSuz

abbrev GL12 : Type := Matrix.GeneralLinearGroup (Fin 12) (ZMod 3)

abbrev Mt : Type := Array ℕ

@[expose] def ofMt (A : Mt) : Matrix (Fin 12) (Fin 12) (ZMod 3) :=
  Matrix.of fun i j => ((A.getD (12 * i.val + j.val) 0 : ℕ) : ZMod 3)

@[expose] def mulM (A B : Mt) : Mt :=
  Array.ofFn (n := 144) fun p =>
    ((List.range 12).foldl
      (fun s j => s + A.getD (12 * (p.val / 12) + j) 0 * B.getD (12 * j + p.val % 12) 0) 0) % 3

@[expose] def oneM : Mt :=
  Array.ofFn (n := 144) fun p => if p.val / 12 = p.val % 12 then 1 else 0

@[expose] def canonB (A : Mt) : Bool := A.size == 144 && A.all (· < 3)

theorem foldl_range_add (f : ℕ → ℕ) (n : ℕ) :
    (List.range n).foldl (fun s j => s + f j) 0 = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]
    rfl

theorem ofMt_mulM (A B : Mt) : ofMt (mulM A B) = ofMt A * ofMt B := by
  ext i k
  have hp : 12 * i.val + k.val < 144 := by omega
  simp only [ofMt, Matrix.of_apply, Matrix.mul_apply]
  rw [mulM, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [hp, dite_true, Option.getD_some]
  have h1 : (12 * i.val + k.val) / 12 = i.val := by omega
  have h2 : (12 * i.val + k.val) % 12 = k.val := by omega
  rw [h1, h2, foldl_range_add, ZMod.natCast_mod, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range
    (fun j => ((A.getD (12 * i.val + j) 0 * B.getD (12 * j + k.val) 0 : ℕ) : ZMod 3))]
  simp [Nat.cast_mul]

theorem ofMt_oneM : ofMt oneM = 1 := by
  ext i k
  have hp : 12 * i.val + k.val < 144 := by omega
  simp only [ofMt, Matrix.of_apply]
  rw [oneM, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [hp, dite_true, Option.getD_some]
  have h1 : (12 * i.val + k.val) / 12 = i.val := by omega
  have h2 : (12 * i.val + k.val) % 12 = k.val := by omega
  rw [h1, h2, Matrix.one_apply]
  by_cases h : i = k
  · subst h
    simp
  · have : i.val ≠ k.val := fun h' => h (Fin.ext h')
    simp [h, this]

theorem canonB_mulM (A B : Mt) : canonB (mulM A B) = true := by
  simp only [canonB, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq]
  refine ⟨by simp [mulM], fun i hi => ?_⟩
  simp only [mulM, Array.getElem_ofFn]
  exact Nat.mod_lt _ (by norm_num)

theorem canonB_oneM : canonB oneM = true := by
  simp only [canonB, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq]
  refine ⟨by simp [oneM], fun i hi => ?_⟩
  simp only [oneM, Array.getElem_ofFn]
  split_ifs <;> norm_num

theorem eq_of_ofMt_eq {A B : Mt} (hA : canonB A = true) (hB : canonB B = true)
    (h : ofMt A = ofMt B) : A = B := by
  simp only [canonB, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq] at hA hB
  obtain ⟨hAs, hAl⟩ := hA
  obtain ⟨hBs, hBl⟩ := hB
  refine Array.ext (hAs.trans hBs.symm) fun p hpA hpB => ?_
  have hp : p < 144 := hAs ▸ hpA
  have key := congrFun (congrFun h ⟨p / 12, by omega⟩) ⟨p % 12, by omega⟩
  simp only [ofMt, Matrix.of_apply] at key
  have e : 12 * (p / 12) + p % 12 = p := by omega
  simp only [e, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hpA,
    Array.getElem?_eq_getElem hpB, Option.getD_some] at key
  have hA3 := hAl p hpA
  have hB3 := hBl p hpB
  have := (ZMod.natCast_eq_natCast_iff' _ _ 3).1 key
  rw [Nat.mod_eq_of_lt hA3, Nat.mod_eq_of_lt hB3] at this
  exact this

@[expose] def mkU (A Ai : Mt) (h1 : mulM A Ai = oneM) (h2 : mulM Ai A = oneM) :
    Matrix.GeneralLinearGroup (Fin 12) (ZMod 3) :=
  ⟨ofMt A, ofMt Ai, by rw [← ofMt_mulM, h1, ofMt_oneM], by rw [← ofMt_mulM, h2, ofMt_oneM]⟩

@[simp] theorem val_mkU (A Ai : Mt) (h1 : mulM A Ai = oneM) (h2 : mulM Ai A = oneM) :
    ((mkU A Ai h1 h2 : Matrix.GeneralLinearGroup (Fin 12) (ZMod 3)) :
      Matrix (Fin 12) (Fin 12) (ZMod 3)) = ofMt A := rfl

structure GenSys where
  mats : Array Mt
  invs : Array Mt

namespace GenSys

@[expose] def letter (G : GenSys) (c : ℕ) : Mt :=
  if c % 2 = 0 then G.mats.getD (c / 2) oneM else G.invs.getD (c / 2) oneM

@[expose] def eval (G : GenSys) (w : List ℕ) : Mt :=
  w.foldl (fun acc c => mulM acc (G.letter c)) oneM

@[expose] def valid (G : GenSys) : Bool :=
  G.mats.size == G.invs.size &&
    (List.range G.mats.size).all fun i =>
      mulM (G.mats.getD i oneM) (G.invs.getD i oneM) == oneM &&
        mulM (G.invs.getD i oneM) (G.mats.getD i oneM) == oneM

theorem mulM_oneM_oneM : mulM oneM oneM = oneM :=
  eq_of_ofMt_eq (canonB_mulM _ _) canonB_oneM (by rw [ofMt_mulM, ofMt_oneM, mul_one])

theorem valid_pair (G : GenSys) (h : G.valid = true) (i : ℕ) :
    mulM (G.mats.getD i oneM) (G.invs.getD i oneM) = oneM ∧
      mulM (G.invs.getD i oneM) (G.mats.getD i oneM) = oneM := by
  simp only [valid, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hs, hall⟩ := h
  by_cases hi : i < G.mats.size
  · exact hall i hi
  · have h1 : G.mats.getD i oneM = oneM := by
      rw [Array.getD_eq_getD_getElem?, Array.getD_getElem?]
      simp [hi]
    have h2 : G.invs.getD i oneM = oneM := by
      rw [Array.getD_eq_getD_getElem?, Array.getD_getElem?]
      have : ¬ i < G.invs.size := by omega
      simp [this]
    rw [h1, h2]
    exact ⟨mulM_oneM_oneM, mulM_oneM_oneM⟩

@[expose] def letterU (G : GenSys) (h : G.valid = true) (c : ℕ) :
    Matrix.GeneralLinearGroup (Fin 12) (ZMod 3) :=
  if c % 2 = 0 then
    mkU (G.mats.getD (c / 2) oneM) (G.invs.getD (c / 2) oneM) (valid_pair G h _).1
      (valid_pair G h _).2
  else
    mkU (G.invs.getD (c / 2) oneM) (G.mats.getD (c / 2) oneM) (valid_pair G h _).2
      (valid_pair G h _).1

@[expose] def evalU (G : GenSys) (h : G.valid = true) (w : List ℕ) :
    Matrix.GeneralLinearGroup (Fin 12) (ZMod 3) :=
  (w.map (G.letterU h)).prod

theorem val_letterU (G : GenSys) (h : G.valid = true) (c : ℕ) :
    ((G.letterU h c : Matrix.GeneralLinearGroup (Fin 12) (ZMod 3)) :
      Matrix (Fin 12) (Fin 12) (ZMod 3)) = ofMt (G.letter c) := by
  unfold letterU letter
  split_ifs <;> rfl

theorem ofMt_foldl (G : GenSys) (h : G.valid = true) (w : List ℕ) (acc : Mt) :
    ofMt (w.foldl (fun a c => mulM a (G.letter c)) acc) =
      ofMt acc * ((w.map (G.letterU h)).prod : Matrix.GeneralLinearGroup (Fin 12) (ZMod 3)) := by
  induction w generalizing acc with
  | nil => simp
  | cons c w ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons, ih, ofMt_mulM,
      Units.val_mul, val_letterU, mul_assoc]

theorem ofMt_eval (G : GenSys) (h : G.valid = true) (w : List ℕ) :
    ofMt (G.eval w) = ((G.evalU h w : Matrix.GeneralLinearGroup (Fin 12) (ZMod 3)) :
      Matrix (Fin 12) (Fin 12) (ZMod 3)) := by
  rw [eval, evalU, ofMt_foldl G h w oneM, ofMt_oneM, one_mul]

end GenSys

end CFSG.EvenSporadicStandard.TwoSuz
