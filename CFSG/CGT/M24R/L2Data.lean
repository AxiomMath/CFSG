module

public import Certificates.Data.CFSGNative.Th.Tables
public import CFSG.CGT.M24R.Words

public section

namespace CFSG.CGT.M24R

open CFSG.Sporadic.Th.Native

@[expose] def gVec : Fin 10 → Fin 16 → Fin 16 :=
  ![![0, 10, 6, 12, 2, 8, 4, 14, 13, 7, 11, 1, 15, 5, 9, 3],
    ![0, 14, 9, 7, 3, 13, 10, 4, 5, 11, 12, 2, 6, 8, 15, 1],
    ![0, 15, 4, 11, 6, 9, 2, 13, 3, 12, 7, 8, 5, 10, 1, 14],
    ![0, 11, 15, 4, 7, 12, 8, 3, 14, 5, 1, 10, 9, 2, 6, 13],
    ![0, 4, 11, 15, 5, 1, 14, 10, 6, 2, 13, 9, 3, 7, 8, 12],
    ![0, 5, 13, 8, 1, 4, 12, 9, 11, 14, 6, 3, 10, 15, 7, 2],
    ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14],
    ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13],
    ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11],
    ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7]]

@[expose] def gInvVec : Fin 10 → Fin 16 → Fin 16 :=
  ![![0, 11, 4, 15, 6, 13, 2, 9, 5, 14, 1, 10, 3, 8, 7, 12],
    ![0, 15, 11, 4, 7, 8, 12, 3, 13, 2, 6, 9, 10, 5, 1, 14],
    ![0, 14, 6, 8, 2, 12, 4, 10, 11, 5, 13, 3, 9, 7, 15, 1],
    ![0, 10, 13, 7, 3, 9, 14, 4, 6, 12, 11, 1, 5, 15, 8, 2],
    ![0, 5, 9, 12, 1, 4, 8, 13, 14, 11, 7, 2, 15, 10, 6, 3],
    ![0, 4, 15, 11, 5, 1, 10, 14, 3, 7, 12, 8, 6, 2, 9, 13],
    ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14],
    ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13],
    ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11],
    ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7]]

@[expose] def gT (j : Fin 10) : Table := Array.ofFn (n := 16) fun p => UInt32.ofNat (gVec j p).val

@[expose] def gTi (j : Fin 10) : Table :=
  Array.ofFn (n := 16) fun p => UInt32.ofNat (gInvVec j p).val

@[expose] def gTc : Array Table := Array.ofFn gT

@[expose] def gTic : Array Table := Array.ofFn gTi

@[expose] def letTab (l : Fin 10 × Bool) : Table := if l.2 then gTc[l.1.val]! else gTic[l.1.val]!

@[expose] def wTab (w : List (Fin 10 × Bool)) : Table :=
  w.foldl (fun X l => compT 16 X (letTab l)) (idT 16)

@[expose] def tw (k : ℕ) : List (Fin 10 × Bool) :=
  (List.finRange 4).flatMap fun j => if k.testBit j.val then [(⟨6 + j.val, by omega⟩, true)] else []

@[expose] def codeOf (X : Table) : ℕ :=
  let v := ap X 0
  v + 16 * ((ap X 1 ^^^ v) + 16 * ((ap X 2 ^^^ v) + 16 * ((ap X 4 ^^^ v) + 16 * (ap X 8 ^^^ v))))

@[expose] def bWord : Fin 2 → List (Fin 10 × Bool) :=
  ![[(2, true), (3, false), (2, true), (4, true), (5, false), (4, true)],
    [(2, true), (3, true), (4, false), (3, true), (5, true), (2, false)]]

@[expose] def dWord10 : Fin 3 → List (Fin 10 × Bool) :=
  ![[(9, true), (0, true), (2, true), (3, false), (5, true), (2, false)],
    [(6, true), (8, true), (2, true), (1, true), (3, true), (5, false), (4, true), (2, false)],
    [(9, true), (0, true), (1, true), (2, true), (5, false), (2, true)]]

@[expose] def thetaWord10 : Fin 3 → List (Fin 10 × Bool) :=
  ![[(0, true), (3, true), (4, false), (5, true), (3, false)],
    [(6, true), (8, true), (9, true), (2, true), (1, true), (4, true), (2, false)],
    [(0, true), (1, true), (3, true), (4, false), (3, true)]]

theorem liftW10_dWord10 (i : Fin 3) : liftW10 (dWord10 i) = dWord i := by
  fin_cases i <;> decide

theorem liftW10_thetaWord10 (i : Fin 3) : liftW10 (thetaWord10 i) = thetaWord i := by
  fin_cases i <;> decide

end CFSG.CGT.M24R
