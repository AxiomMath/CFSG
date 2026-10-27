module

public import CFSG.Certificates.Kernel.EvenSporSuz.Sound
public import Certificates.Data.Kernel.EvenSporSuz.Cover

public section

namespace CFSG.KC.EvenSporSuz

open CFSG.EvenSporadicStandard.TwoSuz CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.SuzMultiplier
open scoped commutatorElement

theorem canonB_invM (A : Array ℕ) : canonB (invM A) = true := by
  unfold invM
  cases (List.range 24).find? fun k => powM A (k + 1) == oneM with
  | none => rw [Option.elim_none]; exact canonB_oneM
  | some k => rw [Option.elim_some]; exact canonB_powM A k

theorem rowsOf_invM {A : Array ℕ} (hA : canonB A = true) : rowsOf (invM A) = invR24 (rowsOf A) := by
  unfold invM invR24
  have hp : (fun k => powM A (k + 1) == oneM) = (fun k => powR (rowsOf A) (k + 1) == oneR) := by
    funext k
    rw [beq_rows (canonB_powM A _) canonB_oneM, rowsOf_powM hA, rowsOf_oneM]
  rw [hp]
  cases (List.range 24).find? fun k => powR (rowsOf A) (k + 1) == oneR with
  | none => rw [Option.elim_none, Option.elim_none]; exact rowsOf_oneM
  | some k => rw [Option.elim_some, Option.elim_some]; exact rowsOf_powM hA k

theorem canonB_negM : canonB negM = true := by
  simp only [canonB, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq]
  refine ⟨by simp [negM], fun i hi => ?_⟩
  simp only [negM, Array.getElem_ofFn]
  split_ifs <;> norm_num

theorem rowsOf_negM : rowsOf negM = negR := by decide +kernel

theorem ofMt_negM : ofMt negM = -1 := by
  ext i k
  have hp : 12 * i.val + k.val < 144 := by omega
  simp only [ofMt, Matrix.of_apply]
  rw [negM, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [hp, dite_true, Option.getD_some]
  have h1 : (12 * i.val + k.val) / 12 = i.val := by omega
  have h2 : (12 * i.val + k.val) % 12 = k.val := by omega
  rw [h1, h2, Matrix.neg_apply, Matrix.one_apply]
  by_cases h : i = k
  · subst h
    simp only [if_true]
    decide
  · have : i.val ≠ k.val := fun h' => h (Fin.ext h')
    simp only [h, this, if_false, Nat.cast_zero, neg_zero]
    decide

variable (G : GenSys) (h : G.valid = true)

theorem evalU_append (a b : List ℕ) : G.evalU h (a ++ b) = G.evalU h a * G.evalU h b := by
  simp only [GenSys.evalU, List.map_append, List.prod_append]

theorem letterU_mul_succ (i : ℕ) : G.letterU h (2 * i) * G.letterU h (2 * i + 1) = 1 := by
  apply Units.ext
  rw [Units.val_mul, GenSys.val_letterU, GenSys.val_letterU, ← ofMt_mulM, Units.val_one]
  have e1 : G.letter (2 * i) = G.mats.getD i oneM := by
    have a1 : 2 * i % 2 = 0 := by omega
    have a2 : 2 * i / 2 = i := by omega
    simp only [GenSys.letter, a1, a2, if_true]
  have e2 : G.letter (2 * i + 1) = G.invs.getD i oneM := by
    have a1 : (2 * i + 1) % 2 ≠ 0 := by omega
    have a2 : (2 * i + 1) / 2 = i := by omega
    simp only [GenSys.letter, a1, a2, if_false]
  rw [e1, e2, (GenSys.valid_pair G h i).1, ofMt_oneM]

theorem letterU_flip (l : Fin gcS × Bool) :
    G.letterU h (2 * l.1.val + if (!l.2) = true then 0 else 1) =
      (G.letterU h (2 * l.1.val + if l.2 = true then 0 else 1))⁻¹ := by
  rcases l with ⟨x, _ | _⟩
  · simp only [Bool.not_false, if_true, Bool.false_eq_true, if_false, Nat.add_zero]
    exact eq_inv_of_mul_eq_one_left (letterU_mul_succ G h x.val)
  · simp only [Bool.not_true, Bool.false_eq_true, if_false, if_true, Nat.add_zero]
    exact eq_inv_of_mul_eq_one_right (letterU_mul_succ G h x.val)

theorem wordCodes_append (a b : List (Fin gcS × Bool)) :
    wordCodes (a ++ b) = wordCodes a ++ wordCodes b := by
  simp only [wordCodes, List.map_append]

theorem evalU_invRev (w : List (Fin gcS × Bool)) :
    G.evalU h (wordCodes (FreeGroup.invRev w)) = (G.evalU h (wordCodes w))⁻¹ := by
  induction w with
  | nil => simp [FreeGroup.invRev, wordCodes, GenSys.evalU]
  | cons l w ih =>
    have e : FreeGroup.invRev (l :: w) = FreeGroup.invRev w ++ [(l.1, !l.2)] := by
      simp [FreeGroup.invRev]
    rw [e, wordCodes_append, evalU_append, ih]
    simp only [wordCodes, GenSys.evalU, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_inv_rev]
    rw [letterU_flip G h l]

theorem evalU_commWord (u v : List (Fin gcS × Bool)) :
    G.evalU h (wordCodes (commWord u v)) =
      ⁅G.evalU h (wordCodes u), G.evalU h (wordCodes v)⁆ := by
  rw [commWord, wordCodes_append, wordCodes_append, wordCodes_append, evalU_append, evalU_append,
    evalU_append, evalU_invRev, evalU_invRev, commutatorElement_def]

theorem eval_eq_oneM_iff (w : List ℕ) : G.eval w = oneM ↔ G.evalU h w = 1 := by
  constructor
  · intro e
    apply Units.ext
    rw [← GenSys.ofMt_eval G h, e, ofMt_oneM, Units.val_one]
  · intro e
    exact eq_of_ofMt_eq (canonB_eval G w) canonB_oneM
      (by rw [GenSys.ofMt_eval G h, e, Units.val_one, ofMt_oneM])

include h in
theorem eval_commWord_of_central (u v : List (Fin gcS × Bool))
    (hv : G.eval (wordCodes v) = oneM ∨ G.eval (wordCodes v) = negM) :
    G.eval (wordCodes (commWord u v)) = oneM := by
  rw [eval_eq_oneM_iff G h, evalU_commWord, commutatorElement_def]
  have hc : ∀ X, X * G.evalU h (wordCodes v) = G.evalU h (wordCodes v) * X := by
    intro X
    rcases hv with e | e
    · rw [(eval_eq_oneM_iff G h _).1 e, mul_one, one_mul]
    · have ev : ((G.evalU h (wordCodes v) : Matrix.GeneralLinearGroup (Fin 12) (ZMod 3)) :
          Matrix (Fin 12) (Fin 12) (ZMod 3)) = -1 := by
        rw [← GenSys.ofMt_eval G h, e, ofMt_negM]
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, ev]
      first
        | exact (Commute.neg_one_right _).eq
        | simp
  rw [hc]
  group

end CFSG.KC.EvenSporSuz
