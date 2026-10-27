module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Data
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParLin

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[expose] def zero6 : Array ℕ := #[0, 0, 0, 0, 0, 0]

@[expose] def diag6 (B : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 6) fun r => B.getD r 0 &&& 2 ^ (r : ℕ)

@[expose] def outer6 (u w : ℕ) : Array ℕ :=
  Array.ofFn (n := 6) fun a => if u.testBit a then w else 0

@[expose] def combo6 (row : ℕ) (C : ℕ → Array ℕ) : ℕ → Array ℕ
  | 0 => zero6
  | k + 1 => if row.testBit k then bxor 6 (combo6 row C k) (C k) else combo6 row C k

@[expose] def gamBlock (ε : Eps) (C : ℕ → Array ℕ) (k : ℕ) : Array ℕ :=
  if k < 6 then bxor 6 (C k) (btr 6 6 (C k))
  else if k < 12 then diag6 (C (k - 6))
  else
    bxor 6 (bxor 6 (combo6 ((genRows ε ((k - 12) / 6)).getD ((k - 12) % 6) 0) C 6)
        (bmul 6 6 (btr 6 6 (genRows ε ((k - 12) / 6)))
          (bmul 6 6 (C ((k - 12) % 6)) (genRows ε ((k - 12) / 6)))))
      (bxor 6 (outer6 ((C 6).getD ((k - 12) / 6) 0)
          ((genRows ε ((k - 12) / 6)).getD ((k - 12) % 6) 0))
        (outer6 ((genRows ε ((k - 12) / 6)).getD ((k - 12) % 6) 0)
          ((C 6).getD ((k - 12) / 6) 0)))

@[expose] def gamFb (ε : Eps) (v : ℕ) : ℕ := packN 6 48 (gamBlock ε (unpackN 6 v))

@[expose] def gamSol (ε : Eps) (m : ℕ) : ℕ :=
  packN 6 7 fun s =>
    if s < 6 then Array.ofFn (n := 6) fun a =>
      (if (a : ℕ) = s then 2 ^ m else 0) ^^^ (if (a : ℕ) = m then 2 ^ s else 0)
    else Array.ofFn (n := 6) fun k => (genRows ε k).getD m 0 ^^^ 2 ^ m

@[expose] def nRels : Eps → ℕ
  | .plus => 21
  | .minus => 16

@[expose] def extRels : Eps → List (List ℕ)
  | .plus => [[0, 0, 0], [1, 1, 1], [2, 2, 2], [3, 3, 3], [4, 4, 4], [5, 5, 5], [0, 1, 0, 1],
      [0, 2, 0, 2], [0, 3, 0, 3], [0, 4, 0, 4], [0, 5, 0, 5], [1, 2, 1, 2], [1, 3, 1, 3],
      [1, 4, 1, 4], [1, 5, 1, 5], [2, 3, 2, 3], [2, 4, 2, 4], [2, 5, 2, 5], [3, 4, 3, 4],
      [3, 5, 3, 5], [4, 5, 4, 5]]
  | .minus => [[0, 0], [1, 1, 1], [2, 2], [3, 3], [4, 4], [0, 1, 0, 1], [0, 2, 0, 2, 0, 2],
      [0, 3, 0, 3], [0, 4, 0, 4], [1, 1, 2, 1, 1, 2, 1, 1, 2], [1, 1, 3, 1, 1, 3],
      [1, 1, 4, 1, 1, 4], [2, 3, 2, 3, 2, 3], [2, 4, 2, 4], [3, 4, 3, 4, 3, 4], [5]]

@[expose] def wordRows (ε : Eps) : List ℕ → Array ℕ
  | [] => id6
  | s :: w => bmul 6 6 (genRows ε s) (wordRows ε w)

@[expose] def urPair6 (ε : Eps) (C : ℕ → Array ℕ) : List ℕ → Array ℕ × Array ℕ
  | [] => (id6, zero6)
  | s :: w =>
    (bmul 6 6 (genRows ε s) (urPair6 ε C w).1,
      bxor 6 (bmul 6 6 (genRows ε s) (urPair6 ε C w).2) (bmul 6 6 (C s) (urPair6 ε C w).1))

@[expose] def extFb (ε : Eps) (v : ℕ) : ℕ :=
  packN 6 (nRels ε) fun k => (urPair6 ε (unpackN 6 v) ((extRels ε).getD k [])).2

@[expose] def cobFb6 (ε : Eps) (v : ℕ) : ℕ :=
  packN 6 6 fun s => bxor 6 (bmul 6 6 (genRows ε s) (unpackN 6 v 0))
    (bmul 6 6 (unpackN 6 v 0) (genRows ε s))

@[expose] def relCheck6 (ε : Eps) : Bool :=
  (extRels ε).length == nRels ε && (extRels ε).all fun w => bIsId 6 (wordRows ε w)

end CFSG.EvenSmallLie.OmegaEight.Stage1
