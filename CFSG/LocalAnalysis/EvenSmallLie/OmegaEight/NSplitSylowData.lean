module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchSData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Data

public section

namespace CFSG.EvenSmallLie.OmegaEight.NSplit

open CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.SpBranch

@[expose] def pBits (v : ℕ) : ℕ :=
  (v &&& 7) ||| (if v.testBit 3 then 32 else 0) ||| (v &&& 16) ||| (if v.testBit 5 then 8 else 0)

@[expose] def jSw (w : ℕ) : ℕ := ((w &&& 7) <<< 3) ||| (w >>> 3 &&& 7)

@[expose] def wEps : Eps → ℕ
  | .plus => 0
  | .minus => 36

@[expose] def kapCode (ε : Eps) (x : ℕ) : ℕ :=
  if x.testBit 6 then (jSw (pBits (x % 64)) ^^^ wEps ε) + 64 else jSw (pBits (x % 64))

@[expose] def kapInvP : Array ℕ :=
  Array.ofFn (n := 128) fun e => ((List.range 128).find? fun x => kapCode .plus x == e).getD 0

@[expose] def kapInvM : Array ℕ :=
  Array.ofFn (n := 128) fun e => ((List.range 128).find? fun x => kapCode .minus x == e).getD 0

@[expose] def kapInv : Eps → ℕ → ℕ
  | .plus, e => kapInvP.getD e 0
  | .minus, e => kapInvM.getD e 0

@[expose] def phiCode (ε : Eps) (i v : ℕ) : ℕ := kapInv ε (sA i (kapCode ε (v + 64))) % 64

@[expose] def actPhi (ε : Eps) (i x : ℕ) : ℕ :=
  if x.testBit 6 then phiCode ε i (x % 64) + 64 else phiCode ε i (x % 64) ^^^ phiCode ε i 0

@[expose] def tCode : Eps → ℕ
  | .plus => 64
  | .minus => 75

@[expose] def p9Orbit (u : ℕ) : List ℕ := ((List.range 512).map fun i => sA i u).dedup

@[expose] def dictCheck (ε : Eps) : Bool :=
  ((List.range 128).all fun x => decide (kapCode ε x < 128) && kapInv ε (kapCode ε x) == x &&
    decide (kapInv ε x < 128) && kapCode ε (kapInv ε x) == x &&
    (List.range 128).all fun y => kapCode ε (x ^^^ y) == (kapCode ε x ^^^ kapCode ε y)) &&
  ((List.range 512).all fun i => (List.range 64).all fun v =>
    decide (phiCode ε i v < 64) && qfB ε (phiCode ε i v) == qfB ε v &&
    phiCode ε (sGinv[i]!) (phiCode ε i v) == v && phiCode ε i (phiCode ε (sGinv[i]!) v) == v &&
    (List.range 64).all fun w =>
      phiCode ε i (v ^^^ w) == (phiCode ε i v ^^^ phiCode ε i w ^^^ phiCode ε i 0)) &&
  ((List.range 512).all fun i => (List.range 128).all fun x =>
    kapInv ε (sA i (kapCode ε x)) == actPhi ε i x) &&
  ((List.range 512).all fun i => i == 0 || (List.range 128).any fun e => sA i e != e) &&
  (List.range 64).all fun v => qfB ε v ||
    ((p9Orbit (kapCode ε (v + 64))).length != 4 ||
      (p9Orbit (kapCode ε (v + 64))).contains (tCode ε))

end CFSG.EvenSmallLie.OmegaEight.NSplit
