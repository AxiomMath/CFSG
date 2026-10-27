module

public import Mathlib.Data.Nat.Notation
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Data1
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Data2
public import CFSG.LieType.Multipliers.U43Data
public import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Data1
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Data2
public meta import CFSG.LieType.Multipliers.U43Data
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Multipliers.ProductKernel
public meta import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U43Action
public meta import CFSG.LieType.Multipliers.U43Action
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs

public section

namespace CFSG.EvenSporadicStandard.M24Std.CU43

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.PairNative
  CFSG.LieType.Multipliers.U43

@[expose] def baseArr : Array ℕ := (chainBase.map Fin.val).toArray

@[expose] def levels : Array Level := rawLevels 820 chainS baseArr

@[expose] def groups : List (List ℕ) := [[0], [1], [2]]

@[expose] def blocks : List (Array (Array ℕ)) := blocksOf 820 levels groups

@[expose] def inP (g : Array ℕ) : Bool := siftA 820 levels baseArr 0 g

@[expose] def powA (n : ℕ) (t : Array ℕ) : ℕ → Array ℕ
  | 0 => idA n
  | e + 1 => compA n t (powA n t e)

@[expose] def tArr (k : ℕ) : Array ℕ :=
  compA 820 (powA 820 phiArr (k / 4)) (powA 820 deltaArr (k % 4))

@[expose] def reps : List (Array ℕ) :=
  [rep0, rep1, rep2, rep3, rep4, rep5, rep6, rep7, rep8]

@[expose] def repCoset : List ℕ := [4, 6, 0, 2, 7, 5, 6, 4, 2]

@[expose] def repCent : List ℕ := [25920, 25920, 1152, 6048, 720, 720, 576, 576, 720]

@[expose] def cosetCount : List (ℕ × ℕ) :=
  [(0, 2836), (2, 5076), (4, 5796), (5, 4536), (6, 5796), (7, 4536)]

@[expose] def sqW (t : Array ℕ) (w : List (Array ℕ)) : Bool :=
  allLt 820 fun i => evR (t :: w) (evR (t :: w) i) == i

@[expose] def commW (t : Array ℕ) (rs : List (Array ℕ)) (w : List (Array ℕ)) : Bool :=
  rs.all fun r => allLt 820 fun i => evR (t :: w) r[i]! == r[evR (t :: w) i]!

@[expose] def permCheck : Bool :=
  (deltaArr :: phiArr :: reps).all (fun t => isInvA 820 t (invCand 820 t)) &&
    (List.range 8).all fun k => isInvA 820 (tArr k) (invCand 820 (tArr k))

@[expose] def normCheck : Bool :=
  [deltaArr, phiArr].all fun u => [tabA, tabB].all fun g =>
    inP (compA 820 u (compA 820 g (invCand 820 u)))

@[expose] def relCheck : Bool :=
  eqA 820 (powA 820 deltaArr 4) (idA 820) && eqA 820 (powA 820 phiArr 2) (idA 820) &&
    eqA 820 (compA 820 phiArr (compA 820 deltaArr phiArr)) (powA 820 deltaArr 3)

@[expose] def cosetCheck : Bool :=
  (List.range 8).all fun k => (List.range 8).all fun k' =>
    (k == k') || !inP (compA 820 (tArr k) (invCand 820 (tArr k')))

@[expose] def multCheck : Bool :=
  (List.range 8).all fun k => (List.range 8).all fun k' => (List.range 8).any fun k'' =>
    eqA 820 (compA 820 (tArr k) (tArr k')) (tArr k'')

@[expose] def repCheck : Bool :=
  (List.range 9).all fun j =>
    eqA 820 (compA 820 reps[j]! reps[j]!) (idA 820) &&
      inP (compA 820 reps[j]! (invCand 820 (tArr repCoset[j]!)))

@[expose] def cosetCounts : Bool :=
  cosetCount.all fun c => countW (sqW (tArr c.1)) blocks [] == c.2

@[expose] def centCounts : Bool :=
  (List.range 9).all fun j => countW (commW (idA 820) [reps[j]!]) blocks [] == repCent[j]!

@[expose] def injCounts : Bool :=
  (List.range 8).all fun k =>
    countW (commW (tArr k) [tabA, tabB]) blocks [] == (if k == 0 then 1 else 0)

end CFSG.EvenSporadicStandard.M24Std.CU43
