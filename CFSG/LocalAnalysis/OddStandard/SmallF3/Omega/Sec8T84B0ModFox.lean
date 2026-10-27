module

public import Certificates.Data.A5GL42

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace T84Mod

open Matrix
open Certificates.A5GL42 (Mat4)

@[expose] def blk (a U : Mat4) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  Matrix.fromBlocks a U 0 a

theorem blk_mul (a U b V : Mat4) : blk a U * blk b V = blk (a * b) (a * V + U * b) := by
  simp [blk, Matrix.fromBlocks_multiply]

theorem blk_one : blk 1 0 = 1 := by
  simp [blk]

theorem blk_inj {a b U V : Mat4} (h : blk a U = blk b V) : a = b ∧ U = V := by
  have h' := (Matrix.fromBlocks_inj).mp h
  exact ⟨h'.1, h'.2.1⟩

@[expose] def wprod (a b : Mat4) (w : List Bool) : Mat4 :=
  (w.map fun c => if c then a else b).prod

theorem wprod_nil (a b : Mat4) : wprod a b [] = 1 := by
  simp [wprod]

theorem wprod_cons (a b : Mat4) (c : Bool) (w : List Bool) :
    wprod a b (c :: w) = (if c then a else b) * wprod a b w := by
  simp [wprod]

@[expose] def wfox (a b U V : Mat4) : List Bool → Mat4
  | [] => 0
  | c :: w => (if c then a else b) * wfox a b U V w + (if c then U else V) * wprod a b w

theorem blk_word (a b U V : Mat4) (w : List Bool) :
    (w.map fun c => if c then blk a U else blk b V).prod =
      blk (wprod a b w) (wfox a b U V w) := by
  induction w with
  | nil => simp [wprod, wfox, blk_one]
  | cons c w ih =>
    rw [List.map_cons, List.prod_cons, ih]
    cases c <;> simp [wprod, wfox, blk_mul, List.prod_cons]

theorem wfox_add (a b U V U' V' : Mat4) (w : List Bool) :
    wfox a b (U + U') (V + V') w = wfox a b U V w + wfox a b U' V' w := by
  induction w with
  | nil => simp [wfox]
  | cons c w ih =>
    cases c <;> simp [wfox, ih, mul_add, add_mul] <;> abel

end T84Mod

end CFSG.OddStandard.SmallF3.Omega
