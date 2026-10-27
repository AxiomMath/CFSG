module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Data

public section

namespace CFSG.EvenSmallLie.OmegaEight.CPrime

open CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight.Stage1

@[expose] def reflB (ε : Eps) (v x : ℕ) : ℕ := x ^^^ (if bfB ε x v then v else 0)

@[expose] def reflRows (ε : Eps) (v : ℕ) : Array ℕ :=
  Array.ofFn (n := 6) fun i => bitsOf 6 fun j => (reflB ε v (2 ^ j)).testBit i

@[expose] def reflRowsCheck (ε : Eps) : Bool :=
  (List.range 64).all fun v => (List.range 64).all fun x =>
    bmulVec 6 6 (reflRows ε v) x == reflB ε v x

@[expose] def reflQfCheck (ε : Eps) : Bool :=
  (List.range 64).all fun v => !qfB ε v ||
    (List.range 64).all fun x => qfB ε (reflB ε v x) == qfB ε x

@[expose] def coneW (ε : Eps) (v : ℕ) : ℕ :=
  ((List.range 64).find? fun w => w != 0 && !qfB ε w && !bfB ε w v).getD 0

@[expose] def sigmaCheck (ε : Eps) : Bool :=
  (List.range 64).all fun v => !qfB ε v ||
    (coneW ε v < 64 && coneW ε v != 0 && !qfB ε (coneW ε v) && !bfB ε (coneW ε v) v &&
      (List.range 64).all fun x =>
        qfB ε (reflB ε (coneW ε v) x ^^^ coneW ε v) == qfB ε x &&
          reflB ε (coneW ε v) (reflB ε v x) ^^^ coneW ε v ==
            reflB ε v (reflB ε (coneW ε v) x ^^^ coneW ε v) &&
          reflB ε (coneW ε v) (reflB ε (coneW ε v) x ^^^ coneW ε v) ^^^ coneW ε v == x)

@[expose] def transN (ε : Eps) (v : ℕ) : ℕ × ℕ :=
  (((List.range 64).flatMap fun n₁ => (List.range 64).map fun n₂ => (n₁, n₂)).find? fun p =>
    qfB ε p.1 && qfB ε p.2 && (p.1 ^^^ p.2) != 0 && (p.1 ^^^ p.2) != v &&
      !bfB ε (p.1 ^^^ p.2) v).getD (0, 0)

@[expose] def transNCheck (ε : Eps) : Bool :=
  (List.range 64).all fun v => !qfB ε v ||
    ((transN ε v).1 < 64 && (transN ε v).2 < 64 && qfB ε (transN ε v).1 &&
      qfB ε (transN ε v).2 && ((transN ε v).1 ^^^ (transN ε v).2) != 0 &&
      ((transN ε v).1 ^^^ (transN ε v).2) != v && !bfB ε ((transN ε v).1 ^^^ (transN ε v).2) v)

@[expose] def sumCheck (ε : Eps) : Bool :=
  (List.range 64).all fun v => (List.range 64).any fun s => !qfB ε s && !qfB ε (v ^^^ s)

@[expose] def order3Check : Bool :=
  bmulVec 6 6 (genRows .plus 0) 1 == 1 &&
    ((List.range 64).all fun x =>
      bmulVec 6 6 (genRows .plus 0) (bmulVec 6 6 (genRows .plus 0)
        (bmulVec 6 6 (genRows .plus 0) x)) == x) &&
    bmulVec 6 6 (genRows .plus 0) 2 != 2

end CFSG.EvenSmallLie.OmegaEight.CPrime
