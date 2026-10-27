module

public import CFSG.Sporadic.Co1Block.TwoBCheckInputs

public section

namespace CFSG.EvenSporadicStandard.G24Aut

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co1Block

@[expose] def parseNums (s : String) : Array Nat :=
  ((s.splitOn " ").filterMap fun t => t.trimAscii.toNat?).toArray

abbrev nn : Nat := 1365

@[expose] def xa : Array Nat := twoBStrong[0]!

@[expose] def ya : Array Nat := twoBStrong[1]!

@[expose] def triTab : Array Nat := CFSG.Sporadic.Co1Block.Native.triTable twoBTris

@[expose] def brayB : List CFSG.Sporadic.Co1Schreier.Native.Rows :=
  CFSG.Sporadic.Co1Block.Native.brayElts (CFSG.Sporadic.Co1Block.Native.brayRows
    CFSG.Sporadic.Co1Schreier.Native.aR twoBD1) twoBBray

@[expose] def sa : Array Nat := CFSG.Sporadic.Co1Block.Native.triPerm triTab twoBTris brayB[5]!

@[expose] def gA : Array (Array Nat) := #[xa, ya, sa]

@[expose] def gAi : Array (Array Nat) := gA.map (invCand nn)

@[expose] def evW (w : List Int) : Array Nat := wordA nn gA gAi w

@[expose] def conjA (c ci t : Array Nat) : Array Nat := compA nn c (compA nn t ci)

@[expose] def conjW (w : List Nat) (t : Array Nat) : Array Nat :=
  let c := evW (w.map Int.ofNat)
  conjA c (invCand nn c) t

@[expose] def buildList (init : Array Nat) (par : Array Nat) (op : Nat → Array Nat → Array Nat) :
    Array (Array Nat) :=
  (List.range par.size).foldl (fun acc k => acc.push (op k acc[par[k]!]!)) #[init]

@[expose] def conjOp (pg : Array Nat) (k : Nat) (t : Array Nat) : Array Nat :=
  conjA gA[pg[k]!]! gAi[pg[k]!]! t

@[expose] def rmulOp (gs : Array (Array Nat)) (pg : Array Nat) (k : Nat) (e : Array Nat) :
    Array Nat :=
  compA nn e gs[pg[k]!]!

@[expose] def pairwiseDistinct (L : Array (Array Nat)) (m : Nat) : Bool :=
  allLt m fun j => allLt j fun i => !(eqA nn L[i]! L[j]!)

@[expose] def conjClosed (L : Array (Array Nat)) (clos : Array Nat) (js : Nat) : Bool :=
  allLt L.size fun k => allLt js fun j =>
    decide (clos[k * js + j]! < L.size) &&
      eqA nn (conjA gA[j]! gAi[j]! L[k]!) L[clos[k * js + j]!]!

@[expose] def rmulClosed (L : Array (Array Nat)) (clos : Array Nat) (gs : Array (Array Nat)) :
    Bool :=
  allLt L.size fun k => allLt gs.size fun j =>
    decide (clos[k * gs.size + j]! < L.size) &&
      eqA nn (compA nn L[k]! gs[j]!) L[clos[k * gs.size + j]!]!

@[expose] def parOK (par pg : Array Nat) (J : Nat) : Bool :=
  allLt par.size fun k => decide (par[k]! ≤ k) && decide (pg[k]! < J)

@[expose] def isInvol (t : Array Nat) : Bool :=
  eqA nn (compA nn t t) (idA nn) && !eqA nn t (idA nn)

@[expose] def conjWEq (w : List Nat) (t target : Array Nat) : Bool :=
  isInvA nn (evW (w.map Int.ofNat)) (invCand nn (evW (w.map Int.ofNat))) &&
    eqA nn (conjW w t) target

@[expose] def fusionOK (j : Nat) (R : Array (Array Nat)) (reps : Array (Array Nat))
    (recs : List (Nat × Nat × List Nat)) : Bool :=
  ((List.range R.size).filter fun k => isInvol R[k]!) == recs.map (·.1) &&
    recs.all fun r => decide (r.2.1 < reps.size) && decide (r.1 < R.size) &&
      lettersOK j (r.2.2.map Int.ofNat) && conjWEq r.2.2 reps[r.2.1]! R[r.1]!

@[expose] def twoBLevels : Array CFSG.Monster.B.Co2.Native.Level :=
  CFSG.Certificates.Native.rawLevels 1365 twoBStrong twoBChainBase.toArray

@[expose] def inD (g : Array Nat) : Bool := siftA nn twoBLevels twoBChainBase.toArray 0 g

@[expose] def inN (g : Array Nat) : Bool :=
  isInvA nn g (invCand nn g) && inD (conjA g (invCand nn g) xa) && inD (conjA g (invCand nn g) ya)

@[expose] def ordAux (t : Array Nat) : Nat → Array Nat → Bool
  | 0, p => eqA nn p (idA nn)
  | d + 1, p => !eqA nn p (idA nn) && ordAux t d (compA nn t p)

@[expose] def ordIs (t : Array Nat) (v : Nat) : Bool := decide (0 < v) && ordAux t (v - 1) t

@[expose] def prodA (ls : Array (Array Nat)) (w : List Nat) : Array Nat :=
  w.foldr (fun l acc => compA nn ls[l]! acc) (idA nn)

@[expose] def testsOK (ls : Array (Array Nat)) (tests : List (List Nat × Nat)) : Bool :=
  tests.all fun t => ordIs (prodA ls t.1) t.2

@[expose] def testsRange (k : Nat) (tests : List (List Nat × Nat)) : Bool :=
  tests.all fun t => t.1.all (· < k) && decide (0 < t.2)

@[expose] def candCount (L : Array (Array Nat)) (base : Array (Array Nat))
    (tests : List (List Nat × Nat)) : Nat :=
  (List.range L.size).countP fun k => testsOK (#[L[k]!] ++ base) tests

@[expose] def readRecs (a : Array Nat) : Nat → Nat → List (Nat × Nat × List Nat)
  | 0, _ => []
  | cnt + 1, p =>
    (a[p]!, a[p + 1]!, (List.range a[p + 2]!).map fun i => a[p + 3 + i]!) ::
      readRecs a cnt (p + 3 + a[p + 2]!)

@[expose] def laNums : Array Nat := parseNums (include_str "G24LATbl.txt")

@[expose] def tAa : Array Nat := laNums.extract 0 1365

@[expose] def laPar : Array Nat := laNums.extract 1365 (1365 + 4094)

@[expose] def laPg : Array Nat := laNums.extract (1365 + 4094) (1365 + 2 * 4094)

@[expose] def laClos : Array Nat := laNums.extract (1365 + 2 * 4094) (1365 + 2 * 4094 + 2 * 4095)

@[expose] def oa : Array Nat :=
  laNums.extract (1365 + 2 * 4094 + 2 * 4095) (1365 + 2 * 4094 + 2 * 4095 + 1365)

@[expose] def laList : Array (Array Nat) := buildList tAa laPar (conjOp laPg)

@[expose] def laOK : Bool :=
  laList.size == 4095 && isInvA nn xa (invCand nn xa) && isInvA nn ya (invCand nn ya) &&
    isInvA nn tAa (invCand nn tAa) && isInvol tAa && parOK laPar laPg 2 &&
    conjClosed laList laClos 2

end CFSG.EvenSporadicStandard.G24Aut
