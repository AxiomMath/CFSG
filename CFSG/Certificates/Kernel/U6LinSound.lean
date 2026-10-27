module

public import Certificates.Data.Kernel.U6.F2K
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParCertW
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParLin
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.KC.U6F2

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2
open CFSG.EvenSmallLie.UnitarySix.YamadaPar (bmul bxor unpackN packN linBits certCheckWith
  injCheckWith)

@[expose] def packM (d : ℕ) (A : Array ℕ) : ℕ :=
  CFSG.EvenSmallLie.UnitarySix.YamadaPar.bitsOf (d * d) fun i => (A.getD (i / d) 0).testBit (i % d)

@[expose] def urPairG (d : ℕ) (I Z : Array ℕ) (gen C : ℕ → Array ℕ) : List ℕ → Array ℕ × Array ℕ
  | [] => (I, Z)
  | s :: w =>
    let p := urPairG d I Z gen C w
    (bmul d d (gen s) p.1, bxor d (bmul d d (gen s) p.2) (bmul d d (C s) p.1))

theorem getLD_eq_getD {α : Type} (x : α) (L : List α) (i : ℕ) : getLD x L i = L.getD i x := by
  induction L generalizing i with
  | nil => rfl
  | cons a L ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem getLD_map_range {α : Type} (x : α) (f : ℕ → α) {n l : ℕ} (hl : l < n) :
    getLD x ((List.range n).map f) l = f l := by
  rw [getLD_eq_getD, List.getD_eq_getElem _ _ (by simpa using hl)]
  simp

theorem orN_congr {k : ℕ} {f g : ℕ → ℕ} (h : ∀ s < k, f s = g s) : orN k f = orN k g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change Nat.lor (f k) (orN k f) = Nat.lor (g k) (orN k g)
    rw [h k (Nat.lt_succ_self k), ih fun s hs => h s (Nat.lt_succ_of_lt hs)]

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

theorem shiftRight_lor_shiftLeft {P U n : ℕ} (hP : P < 2 ^ n) :
    Nat.shiftRight (Nat.lor P (Nat.shiftLeft U n)) n = U := by
  apply Nat.eq_of_testBit_eq
  intro i
  change ((P ||| U <<< n) >>> n).testBit i = U.testBit i
  rw [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hP (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  simp

theorem packBlks_eq (k : ℕ) (f : ℕ → Array ℕ) :
    CFSG.EvenSmallLie.UnitarySix.YamadaPar.packBlks k f = packN 8 k f := rfl

theorem unpackBlk_eq (v s : ℕ) :
    CFSG.EvenSmallLie.UnitarySix.YamadaPar.unpackBlk v s = unpackN 8 v s := rfl

end CFSG.KC.U6F2

end
