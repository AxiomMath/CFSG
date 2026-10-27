module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutTables
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import Certificates.Data.CFSGNative.SmallOddCore.Check

public section

namespace CFSG.EvenSmallLie.OmegaEight

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.ComponentClassification.J2Cover (arrTable chainTables)

@[expose] def qNat (v : ℕ) : Bool :=
  (v.testBit 0 && v.testBit 4) ^^ (v.testBit 1 && v.testBit 5) ^^
    (v.testBit 2 && v.testBit 6) ^^ (v.testBit 3 && v.testBit 7)

@[expose] def bNat (v w : ℕ) : Bool :=
  ((v.testBit 0 && w.testBit 4) ^^ (w.testBit 0 && v.testBit 4)) ^^
    ((v.testBit 1 && w.testBit 5) ^^ (w.testBit 1 && v.testBit 5)) ^^
    ((v.testBit 2 && w.testBit 6) ^^ (w.testBit 2 && v.testBit 6)) ^^
    ((v.testBit 3 && w.testBit 7) ^^ (w.testBit 3 && v.testBit 7))

@[expose] def eichNat (u w x : ℕ) : ℕ :=
  x ^^^ (if bNat x u then w else 0) ^^^ (if bNat x w then u else 0) ^^^
    (if qNat w && bNat x u then u else 0)

@[expose] def transNat (v x : ℕ) : ℕ := if bNat x v then x ^^^ v else x

@[expose] def nsList : List ℕ := (List.range 256).filter qNat

@[expose] def nsArr : Array ℕ := nsList.toArray

@[expose] def nsIdx : Array ℕ := Array.ofFn (n := 256) fun v => nsList.idxOf v.val

@[expose] def nsCheck : Bool :=
  nsArr.size == 120 && nsIdx.size == 256 &&
    (List.range 120).all (fun j => decide (nsArr[j]! < 256) && qNat nsArr[j]! &&
      nsIdx[nsArr[j]!]! == j) &&
    (List.range 256).all fun v => !qNat v || (decide (nsIdx[v]! < 120) && nsArr[nsIdx[v]!]! == v)

@[expose] def rootArr (p : List (ℕ × ℕ)) : Array ℕ :=
  Array.ofFn (n := 360) fun i =>
    120 * (i.val / 120) +
      nsIdx[eichNat (p.getD (i.val / 120) (0, 0)).1 (p.getD (i.val / 120) (0, 0)).2
        nsArr[i.val % 120]!]!

@[expose] def rhoArr : Array ℕ := Array.ofFn (n := 360) fun i => (i.val + 120) % 360

@[expose] def tauArr : Array ℕ :=
  Array.ofFn (n := 360) fun i =>
    120 * ((3 - i.val / 120) % 3) + nsIdx[transNat 136 nsArr[i.val % 120]!]!

@[expose] def rootPairs : List (List (ℕ × ℕ)) :=
  [[(1, 32), (4, 8), (4, 128)], [(2, 16), (64, 128), (8, 64)], [(2, 64), (2, 64), (2, 64)],
    [(4, 32), (4, 32), (4, 32)], [(4, 128), (1, 32), (4, 8)], [(8, 64), (2, 16), (64, 128)],
    [(4, 8), (4, 128), (1, 32)], [(64, 128), (8, 64), (2, 16)]]

@[expose] def genArrs : Array (Array ℕ) := (rootPairs.map rootArr).toArray ++ #[rhoArr, tauArr]

@[expose] def copy0Arr (t : Array ℕ) : Array ℕ := Array.ofFn (n := 120) fun i => t[i.val]!

@[expose] def pushWords (n : ℕ) (S : Array (Array ℕ)) : List (List ℤ) → Array (Array ℕ)
  | [] => S
  | w :: ws => pushWords n (S.push (wordA n S (rawInvs n S) w)) ws

@[expose] def wordsOf (k : ℕ) (D : List (List ℤ)) : Array (List ℤ) :=
  (List.replicate k [] ++ D).toArray

@[expose] def omegaWords : List (List ℤ) :=
  [[-3, 5, 3], [-9, 7, 9], [-7, -3, 7, 3], [-6, 4, 6], [-8, 4, 8], [-1, -2, -4, 10, 2, 1],
    [-7, -10, -14, -3, 14, 3], [-11, -15, -7, -14, -12, 15, 12], [-13, -11, 15, 13]]

@[expose] def omegaS : Array (Array ℕ) := pushWords 360 (genArrs.extract 0 8) omegaWords

@[expose] def omegaBase : List (Fin 360) := [0, 2, 1, 4, 24, 8, 9]

@[expose] def autWords : List (List ℤ) :=
  [[-3, 5, 3], [-7, -10, 11, 10], [-5, 12, 5], [-6, 4, 6], [-1, -2, -13, 14, 2, 1],
    [-12, -5, 15, 5], [-11, 15, 11], [-17, -15, -10, -15, 10, 15, 10]]

@[expose] def autS : Array (Array ℕ) := pushWords 360 genArrs autWords

@[expose] def autBase : List (Fin 360) := [0, 2, 1, 4, 24, 8, 9]

@[expose] def omega1S : Array (Array ℕ) :=
  pushWords 120 ((genArrs.extract 0 8).map copy0Arr) omegaWords

@[expose] def omega1Base : List (Fin 120) := [0, 2, 1, 4, 24, 8, 9]

@[expose] def sylowIdx : List ℕ := [0, 2, 4, 6, 9]

@[expose] def sylowGens : Array (Array ℕ) := sylowIdx.toArray.map fun i => genArrs[i]!

@[expose] def sylowWords : List (List ℤ) := [[-2, 3, 2], [-4, -5, 6, 5], [-3, 7, 3]]

@[expose] def sylowS : Array (Array ℕ) := pushWords 360 sylowGens sylowWords

@[expose] def sylowBase : List (Fin 360) := [0, 2, 4, 24, 8]

@[expose] def omegaChainCheck : Bool :=
  rawChainOK 360 (omegaS.extract 0 8) omegaS (omegaBase.map Fin.val).toArray
      (wordsOf 8 omegaWords) 4 &&
    rawOrbitSizes 360 omegaS (omegaBase.map Fin.val).toArray == [120, 63, 30, 12, 8, 4, 2]

@[expose] def autChainCheck : Bool :=
  rawChainOK 360 (autS.extract 0 10) autS (autBase.map Fin.val).toArray (wordsOf 10 autWords) 4 &&
    rawOrbitSizes 360 autS (autBase.map Fin.val).toArray == [360, 63, 30, 12, 8, 4, 4]

@[expose] def omega1ChainCheck : Bool :=
  rawChainOK 120 (omega1S.extract 0 8) omega1S (omega1Base.map Fin.val).toArray
      (wordsOf 8 omegaWords) 4 &&
    rawOrbitSizes 120 omega1S (omega1Base.map Fin.val).toArray == [120, 63, 30, 12, 8, 4, 2]

@[expose] def sylowChainCheck : Bool :=
  rawChainOK 360 (sylowS.extract 0 5) sylowS (sylowBase.map Fin.val).toArray
      (wordsOf 5 sylowWords) 4 &&
    rawOrbitSizes 360 sylowS (sylowBase.map Fin.val).toArray == [64, 2, 8, 4, 2]

@[expose] def omegaW (w : List ℤ) : Array ℕ := wordA 360 omegaS (rawInvs 360 omegaS) w

@[expose] def autW (w : List ℤ) : Array ℕ := wordA 360 autS (rawInvs 360 autS) w

@[expose] def sylowW (w : List ℤ) : Array ℕ := wordA 360 sylowS (rawInvs 360 sylowS) w

@[expose] def conjArr (t u : Array ℕ) : Array ℕ := compA 360 (compA 360 t u) (invCand 360 t)

@[expose] def commArr (t u : Array ℕ) : Bool := eqA 360 (compA 360 t u) (compA 360 u t)

@[expose] def powArr (t : Array ℕ) : ℕ → Array ℕ
  | 0 => idA 360
  | k + 1 => compA 360 t (powArr t k)

@[expose] def rhoPerm : List ℕ := [4, 5, 2, 3, 6, 7, 0, 1]

@[expose] def tauPerm : List ℕ := [0, 1, 2, 3, 6, 7, 4, 5]

@[expose] def structureCheck : Bool :=
  (List.range 8).all (fun i =>
    eqA 360 (conjArr genArrs[8]! genArrs[i]!) genArrs[rhoPerm.getD i 0]! &&
      eqA 360 (conjArr genArrs[9]! genArrs[i]!) genArrs[tauPerm.getD i 0]! &&
      (List.range 360).all fun p => decide (p < 120) == decide ((genArrs[i]!)[p]! < 120)) &&
    (List.range 360).all fun p => (genArrs[8]!)[p]! == (p + 120) % 360

@[expose] def stabIdx : List ℕ := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]

@[expose] def stabCheck : Bool :=
  stabIdx.all (fun j => decide (j < omegaS.size) && (omegaS[j]!)[0]! == 0) &&
    (List.range 359).all fun p => stabIdx.any fun j => (omegaS[j]!)[p + 1]! != p + 1

@[expose] def bfsTree : Array ℕ × Array ℕ × Array ℕ := Id.run do
  let mut par : Array ℕ := Array.replicate 120 0
  let mut lab : Array ℕ := Array.replicate 120 0
  let mut dep : Array ℕ := (Array.replicate 120 1000).set! 0 0
  let mut queue : Array ℕ := #[0]
  let mut h := 0
  for _ in [0:120] do
    if h < queue.size then
      let x := queue[h]!
      h := h + 1
      for l in [0:8] do
        let y := (genArrs[l]!)[x]!
        if y < 120 && dep[y]! == 1000 then
          dep := dep.set! y (dep[x]! + 1)
          par := par.set! y x
          lab := lab.set! y l
          queue := queue.push y
  return (par, lab, dep)

@[expose] def treeOK (par lab dep : Array ℕ) : Bool :=
  dep[0]! == 0 &&
    (List.range 119).all fun i =>
      decide (par[i + 1]! < 120) && decide (lab[i + 1]! < 8) &&
        decide (dep[par[i + 1]!]! < dep[i + 1]!) && (genArrs[lab[i + 1]!]!)[par[i + 1]!]! == i + 1

@[expose] def treeCheck : Bool := treeOK bfsTree.1 bfsTree.2.1 bfsTree.2.2

@[expose] def sylowTables : List (List Table) :=
  chainTables 360 sylowS (sylowBase.map Fin.val).toArray

@[expose] def sylowGensT : Array Table := sylowGens.map (arrTable 360)

@[expose] def sylowGensInvT : Array Table := sylowGens.map fun t => arrTable 360 (invCand 360 t)

@[expose] def invList : List Table := filterProducts 360 (ordTest 360 2) sylowTables (idT 360) []

@[expose] def fourList : List Table := filterProducts 360 (ordTest 360 4) sylowTables (idT 360) []

@[expose] def repWords : List (List ℤ) :=
  [[4], [8, 7], [7], [6, 3, 7], [3, 4], [5], [5, 8, 7], [2], [2, 8, 7], [2, 5],
   [1, 2, 1, 8, 1, 2, 1, 8], [1, 2, 1, 8, 1, 2, 1, 8, 4], [1, 2, 1, 8, 1, 2, 1, 6, 8, 4, 7],
   [1, 2, 1, 8, 1, 2, 1, 5, 8], [1, 8, 7, 1, 8, 7], [1, 8, 7, 1, 8], [1, 8, 7, 1, 6, 3, 8],
   [1, 8, 7, 1, 5, 3, 8, 4, 7], [1, 7, 1, 7], [1, 7, 1, 8], [1, 7, 1, 2, 7], [1, 7, 1, 2, 8], [1],
   [1, 4], [1, 3, 4], [1, 5], [2, 1, 8, 1, 2, 1, 8], [2, 1, 8, 1, 2, 1, 8, 4], [1, 2, 1, 2],
   [1, 2, 1, 2, 7], [1, 2, 1, 2, 6, 3, 7], [1, 2, 1, 2, 5], [1, 2, 1, 6, 3, 7],
   [2, 1, 8, 4, 2, 1, 8, 4, 7], [2, 1, 8, 4, 2, 1, 8, 4], [2, 1, 8, 4, 2, 1, 2, 6, 3, 8, 4, 7],
   [7, 1, 7, 6, 1, 6], [7, 1, 7, 6, 1, 6, 8, 7]]

@[expose] def repArrs : List (Array ℕ) := repWords.map sylowW

@[expose] def repTypes : List ℕ :=
  [0, 0, 0, 1, 1, 3, 4, 0, 1, 4, 0, 1, 2, 4, 0, 1, 2, 4, 0, 1, 1, 2, 0, 1, 2, 4, 1, 2, 0, 1, 2, 4,
   2, 1, 2, 2, 1, 2]

@[expose] def mainWords : List (List ℤ) :=
  [[1, 2, 1, 8, 1, 2, 1, 8], [7, 1, 7, 6, 1, 6], [7, 1, 7, 6, 1, 6, 8, 7], [5],
   [1, 2, 1, 8, 1, 2, 1, 5, 8]]

@[expose] def mainArrs : List (Array ℕ) := mainWords.map sylowW

@[expose] def conjWords : List (List ℤ) :=
  [[3, 5, 4, 6, 1, 3, 2, 4], [1, 3, 2, 4], [5, 6, 1, 3, 2, 4], [1, 2], [3, 4, 1, 2], [],
   [5, 1, 3, 2, 4], [7, 8, 5, 6, 1, 3, 2, 4], [5, 6, 5, 1, 2], [7, 8, 5, 6, 5, 1, 3, 2, 4], [],
   [9, 9, 3, 5, 4, 6, 3, 5], [4, 3, 1, 2], [], [3, 4], [9, 9, 5, 6, 5], [1, 2, 1], [3, 4],
   [5, 6, 3, 4], [9, 9], [9, 5, 6, 5, 1, 2], [5, 6, 1, 2], [3, 7, 4, 8, 5, 6, 3, 4],
   [9, 3, 4, 1, 2], [3, 7, 4, 8, 5, 6, 1, 2, 1], [3, 7, 4, 8, 5, 6, 5, 3, 4], [3, 5, 4, 6, 3, 5],
   [3, 5, 4, 6, 3, 1], [7, 8, 5, 6, 3, 4], [9, 1, 2], [7, 8, 5, 6, 1, 2, 1],
   [7, 8, 5, 6, 5, 3, 4], [7, 8, 5, 6, 1, 2], [5, 6, 5], [5, 6, 1], [8, 6, 1], [], []]

@[expose] def conjArrs : List (Array ℕ) := conjWords.map autW

@[expose] def sylowRepsCheck : Bool :=
  repsOK 360 sylowGensT sylowGensInvT invList (repArrs.map (arrTable 360)) 100 &&
    repArrs.all (fun r => ordTest 360 2 (arrTable 360 r)) &&
    (List.range 38).all fun j =>
      siftA 360 (rawLevels 360 omegaS (omegaBase.map Fin.val).toArray)
          (omegaBase.map Fin.val).toArray 0 (repArrs.getD j #[]) ==
        decide (repTypes.getD j 0 < 3) &&
      eqA 360 (conjArr (conjArrs.getD j #[]) (mainArrs.getD (repTypes.getD j 0) #[]))
        (repArrs.getD j #[])

@[expose] def cent0Words : List (List (List ℤ)) :=
  [[[7, 1, 3, 1, 6, 7, 11], [2, 1, 3, 1, 3, 15, 11], [7, 1, 3, 1, 7],
     [3, 1, 2, 8, 12, 3, 9, 12, 4, 9, 5, 10, 15]],
    [[12, 1, 2, 17, 12, 8, 11, 13, 9, 15, 16], [9, 11, 1, 3, 12, 8, 11, 13, 10, 7],
     [14, 3, 2, 1, 13, 6, 9, 12, 9, 5, 14, 7, 15, 11], [1, 3, 2, 17, 1, 13, 3, 11, 17, 15]],
    [[9, 11, 1, 4, 5, 7], [13, 4, 2, 13, 3, 4, 17, 5, 7, 15], [1, 11, 1, 9, 7], [5, 1, 3, 1, 5]],
    [[16, 17, 9, 14, 7, 16], [2, 1, 3, 1, 4, 8, 6, 15, 9, 13, 12, 9, 5, 10, 15],
     [4, 6, 17, 6, 4, 16, 17, 9, 14, 7, 15, 11, 16], [1, 2, 15, 13, 9, 12, 9, 5, 11]],
    [[10, 8, 12, 3, 9, 12, 4, 9, 7, 11], [13, 2, 1, 8, 6, 5, 10, 15, 11, 16],
     [4, 2, 4, 14, 7, 15, 11], [1, 3, 1, 8, 6]]]

@[expose] def cent0Check : Bool :=
  (List.range 5).all fun i =>
    (cent0Words.getD i []).all fun w => commArr (omegaW w) (mainArrs.getD i #[])

@[expose] def repGens (j : ℕ) : List (Array ℕ) :=
  (cent0Words.getD (repTypes.getD j 0) []).map (fun w => conjArr (conjArrs.getD j #[]) (omegaW w))
    ++ [repArrs.getD j #[]]

@[expose] def fiveOK (GT GI : Array Table) (b : Table)
    (c : Array Table × Array ℕ × Array ℕ) : Bool :=
  conjTreeOK 360 GT GI b c.1 c.2.1 c.2.2 && hkeysDistinct 360 c.1.toList && decide (5 ≤ c.1.size)

@[expose] def closureCheckAt (j : ℕ) : Bool :=
  let GT := ((repGens j).map (arrTable 360)).toArray
  let GI := ((repGens j).map fun t => arrTable 360 (invCand 360 t)).toArray
  let y := arrTable 360 (repArrs.getD j #[])
  fourList.all fun b => !commT 360 b y || fiveOK GT GI b (conjClosureH 360 GT GI b 5)

@[expose] def closureCheck : Bool := (List.range 38).all closureCheckAt

@[expose] def fgWords : List (List ℤ) :=
  [[12, 11, 9, 2, 1, 6, 13, 3, 12, 17, 12, 4, 11, 17, 14, 10, 15, 11, 16], [7, 5, 3, 1, 8, 6, 9]]

@[expose] def fgCheck : Bool :=
  (List.range 2).all fun i =>
    let x := mainArrs.getD (i + 3) #[]
    let l := omegaW (fgWords.getD i [])
    let v := compA 360 (conjArr l x) x
    eqA 360 (compA 360 v v) (idA 360) && !eqA 360 v (idA 360)

@[expose] def oddData : List (List ℤ × List ℤ × ℕ × ℕ × ℕ) :=
  [([1, 2, 8, 7], [1, 10, 5, 3, 1, 8, 6, 3, 10, 7], 6, 3, 3),
   ([1, 10, 1, 4, 8, 5, 6, 9, 10, 11], [14, 13, 3, 2, 1, 6, 13, 6, 16, 13, 9, 7, 15, 16], 5, 5, 5),
   ([9, 1, 3, 4, 9], [14, 4, 3, 2, 1, 3, 14, 10, 7, 15, 11], 3, 3, 3)]

@[expose] def oddCheck : Bool :=
  (List.range 3).all fun i =>
    let d := oddData.getD i ([], [], 0, 0, 0)
    let x := mainArrs.getD i #[]
    let u := omegaW d.1
    let v := omegaW d.2.1
    d.2.2.2.1 % 2 == 1 && d.2.2.2.2 % 2 == 1 &&
      ordTest 360 d.2.2.2.1 (arrTable 360 u) && ordTest 360 d.2.2.2.2 (arrTable 360 v) &&
      commArr u x && commArr v x && eqA 360 (powArr (compA 360 u v) d.2.2.1) x

@[expose] def invsCheck : Bool :=
  (List.range 38).all (fun j => (repGens j).all fun t => isInvA 360 t (invCand 360 t)) &&
    (conjArrs ++ mainArrs ++ repArrs).all (fun t => isInvA 360 t (invCand 360 t)) &&
    cent0Words.all (fun ws => ws.all fun w => isInvA 360 (omegaW w) (invCand 360 (omegaW w))) &&
    fgWords.all fun w => isInvA 360 (omegaW w) (invCand 360 (omegaW w))

end CFSG.EvenSmallLie.OmegaEight
