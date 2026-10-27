module

public import CFSG.Sporadic.Co1.Module.OddCentCardInputs

public section

namespace CFSG.EvenSporadicStandard.TwoB.MW3

open CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.Odd CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.OddNative

@[expose] def extraLines : List (List (ℕ × ℕ)) := [
  [],
  [(6, 1), (10, 1)],
  [(6, 1), (14, 1)],
  [(10, 1), (6, 1)],
  [(10, 1), (14, 1)],
  [(14, 1), (6, 1)],
  [(14, 1), (10, 1)],
  [(14, 1), (14, 1)],
  [(6, 1), (10, 1), (6, 1)],
  [(6, 1), (10, 1), (14, 1)],
  [(6, 1), (14, 1), (6, 1)],
  [(6, 1), (14, 1), (10, 1)],
  [(10, 1), (6, 1), (14, 1)],
  [(10, 1), (14, 1), (6, 1)],
  [(10, 1), (14, 1), (10, 1)],
  [(10, 1), (14, 1), (14, 1)],
  [(14, 1), (6, 1), (10, 1)],
  [(14, 1), (6, 1), (14, 1)],
  [(14, 1), (10, 1), (6, 1)],
  [(14, 1), (10, 1), (14, 1)],
  [(14, 1), (14, 1), (6, 1)],
  [(14, 1), (14, 1), (10, 1)]]

@[expose] def progM : List (List (ℕ × ℕ)) := prog3 ++ extraLines

@[expose] def regsRowsM : Array (Array ℕ) := runRows initRows3 progM

@[expose] def rrM (i : ℕ) : Array ℕ := regsRowsM[i]?.getD (idRows 24)

@[expose] def cycIdx : List ℕ :=
  [15, 6, 10, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33, 34, 35, 36]

@[expose] def relIdx : List ℕ := [32, 6, 23, 25]

@[expose] def vec0 : ℕ := 12868317

@[expose] def coef1 : ℕ := 8912896

@[expose] def coef2 : ℕ := 524288

@[expose] def sInvRows : Array ℕ := #[
  1276598, 11404553, 15691923, 4975464, 14211351, 12779531,
  2205536, 11104194, 8114968, 4361048, 10941735, 16070228,
  10237510, 11237632, 291754, 856040, 2552033, 16580959,
  12908605, 7649949, 9848481, 15804339, 9339714, 1368524]

@[expose] def cRows : Array ℕ := #[
  16364060, 925520, 15569944, 5241408, 11812629, 14323677,
  7921808, 10529240, 5364753, 3916360, 13745361, 9091336,
  2084233, 5362120, 1673236, 14940481, 8669137, 12273432,
  3186048, 0, 3931521, 6253784, 5849481, 0]

@[expose] def actRows (M : Array ℕ) (v : ℕ) : ℕ := vecMulN 24 (transposeRows 24 M) v

@[expose] def sumRows (l : List ℕ) : Array ℕ :=
  l.foldl (fun acc i => addRows acc (rrM i)) (Array.replicate 24 0)

@[expose] def sRows : Array ℕ := (cycIdx.map fun i => actRows (rrM i) vec0).toArray

@[expose] def eRows : Array ℕ := Array.ofFn (n := 24) fun i =>
  (if vec0.testBit i then coef1 else 0) ^^^ (if (actRows (rr 27) vec0).testBit i then coef2 else 0)

@[expose] def commOK : Bool :=
  (cycIdx ++ relIdx).all (fun i => mulRows 24 (rrM i) (rr 27) == mulRows 24 (rr 27) (rrM i)) &&
    (mulRows 24 (transposeRows 24 sRows) sInvRows == idRows 24) &&
    (actRows (sumRows relIdx) vec0 == 0) &&
    (addRows (mulRows 24 cRows (sumRows relIdx)) (idRows 24) == eRows)

end CFSG.EvenSporadicStandard.TwoB.MW3
