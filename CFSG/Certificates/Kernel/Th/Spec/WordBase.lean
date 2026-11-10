
module

public import CFSG.Certificates.Kernel.Th.Spec.RowsBase

@[expose] public section

namespace CFSG.KC.Th.Spec

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier

def wordCode (l : ℤ) : ℕ := if l = 1 ∨ l = -1 then 0 else if l = 2 then 1 else 2

def codeLetter {M : Type*} (a b bi : M) (x : ℕ) : M :=
  if x = 0 then a else if x = 1 then b else bi

theorem pkMat_wordLetter (A B Bi x : ℕ) :
    pkMat (wordLetter A B Bi x) = codeLetter (pkMat A) (pkMat B) (pkMat Bi) x := by
  unfold wordLetter codeLetter
  split_ifs <;> rfl

section Consts

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
  (K : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)

include K in
theorem pk_wordAB (A B Bi w n : ℕ) :
    pkMat (wordAB c rm ONE A B Bi w n) =
      ((List.range n).map fun i =>
        codeLetter (pkMat A) (pkMat B) (pkMat Bi) (bitsN w (2 * i) 2)).prod := by
  induction n with
  | zero => rw [pkMat_wordAB_zero K]; rfl
  | succ n ih =>
    rw [pkMat_wordAB_succ K, ih, pkMat_wordLetter, List.range_succ, List.map_append,
      List.prod_append, List.map_singleton, List.prod_singleton]

end Consts

theorem rowsMatrix_lett3 (P Q : Array V4) (l : ℤ) :
    rowsMatrix (if l = 1 ∨ l = -1 then P else if l = 2 then Q else Native.mulRows Q Q) =
      codeLetter (rowsMatrix P) (rowsMatrix Q) (rowsMatrix Q * rowsMatrix Q) (wordCode l) := by
  unfold wordCode codeLetter
  by_cases h1 : l = 1 ∨ l = -1
  · simp [h1]
  · by_cases h2 : l = 2
    · simp [h1, h2]
    · simp [h1, h2, rowsMatrix_mulRows]

theorem wfRows_lett3 {P Q : Array V4} (hP : WfRows P) (hQ : WfRows Q) (l : ℤ) :
    WfRows (if l = 1 ∨ l = -1 then P else if l = 2 then Q else Native.mulRows Q Q) := by
  by_cases h1 : l = 1 ∨ l = -1
  · simpa [h1] using hP
  · by_cases h2 : l = 2
    · simpa [h1, h2] using hQ
    · simpa [h1, h2] using hQ.mulRows hQ

end CFSG.KC.Th.Spec

end
