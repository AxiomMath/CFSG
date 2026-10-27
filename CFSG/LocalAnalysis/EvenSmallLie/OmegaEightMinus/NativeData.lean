module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData

public section

namespace CFSG.EvenSmallLie.OmegaEightMinus

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.ComponentClassification.J2Cover (arrTable chainTables)
open CFSG.EvenSmallLie.OmegaEight (pushWords wordsOf)

@[expose] def qNat (v : ℕ) : Bool :=
  (v.testBit 0 && v.testBit 3) ^^ (v.testBit 1 && v.testBit 4) ^^ (v.testBit 2 && v.testBit 5) ^^
    (v.testBit 6 ^^ (v.testBit 6 && v.testBit 7) ^^ v.testBit 7)

@[expose] def bNat (v w : ℕ) : Bool :=
  ((v.testBit 0 && w.testBit 3) ^^ (w.testBit 0 && v.testBit 3)) ^^
    ((v.testBit 1 && w.testBit 4) ^^ (w.testBit 1 && v.testBit 4)) ^^
    ((v.testBit 2 && w.testBit 5) ^^ (w.testBit 2 && v.testBit 5)) ^^
    ((v.testBit 6 && w.testBit 7) ^^ (w.testBit 6 && v.testBit 7))

@[expose] def eichNat (u w x : ℕ) : ℕ :=
  x ^^^ (if bNat x u then w else 0) ^^^ (if bNat x w then u else 0) ^^^
    (if qNat w && bNat x u then u else 0)

@[expose] def transNat (v x : ℕ) : ℕ := if bNat x v then x ^^^ v else x

@[expose] def nsList : List ℕ := (List.range 256).filter qNat

@[expose] def nsArr : Array ℕ := nsList.toArray

@[expose] def nsIdx : Array ℕ := Array.ofFn (n := 256) fun v => nsList.idxOf v.val

@[expose] def nsCheck : Bool :=
  nsArr.size == 136 && nsIdx.size == 256 &&
    (List.range 136).all (fun j => decide (nsArr[j]! < 256) && qNat nsArr[j]! &&
      nsIdx[nsArr[j]!]! == j) &&
    (List.range 256).all fun v => !qNat v || (decide (nsIdx[v]! < 136) && nsArr[nsIdx[v]!]! == v)

@[expose] def eichArr (p : ℕ × ℕ) : Array ℕ :=
  Array.ofFn (n := 136) fun i => nsIdx[eichNat p.1 p.2 nsArr[i.val]!]!

@[expose] def reflArr : Array ℕ := Array.ofFn (n := 136) fun i => nsIdx[transNat 64 nsArr[i.val]!]!

@[expose] def gPairs : List (ℕ × ℕ) :=
  [(1, 16), (2, 8), (2, 32), (4, 16), (4, 64), (4, 128), (4, 192), (32, 64), (32, 128), (32, 192)]

@[expose] def genArrs : Array (Array ℕ) := (gPairs.map eichArr).toArray ++ #[reflArr]

@[expose] def omegaWords : List (List ℤ) :=
  [[-3, 5, 3], [-7, 11, 6], [-6, -12, -3, 6, 3], [-5, -10, 6, 8], [-3, -4, 8, 4, 3],
    [-15, -12, -1, -12, 15, 2], [-4, 16, 4], [-16, -15, -16, 15, 16, 15]]

@[expose] def omegaS : Array (Array ℕ) := pushWords 136 (genArrs.extract 0 10) omegaWords

@[expose] def omegaBase : List (Fin 136) := [0, 2, 1, 12, 4, 28, 5]

@[expose] def autWords : List (List ℤ) :=
  [[-3, 5, 3], [-7, 12, 6], [-13, -6, -13, -3, 6, 3], [-11, -5, -10, 6, 8], [-3, -4, 8, 4, 3],
    [-16, -13, -1, -13, 16, 2], [-4, 17, 4], [-17, -11, -16, -17, 16, 17, 16]]

@[expose] def autS : Array (Array ℕ) := pushWords 136 genArrs autWords

@[expose] def autBase : List (Fin 136) := [0, 2, 1, 12, 64, 4, 28, 5]

@[expose] def sylowIdx : List ℕ := [0, 2, 4, 5, 6, 10]

@[expose] def sylowGens : Array (Array ℕ) := sylowIdx.toArray.map fun i => genArrs[i]!

@[expose] def sylowWords : List (List ℤ) := [[-2, 3, 2], [-5, 7, 4], [-8, -4, -8, -2, 4, 2]]

@[expose] def sylowS : Array (Array ℕ) := pushWords 136 sylowGens sylowWords

@[expose] def sylowBase : List (Fin 136) := [0, 2, 12, 64, 4]

@[expose] def omegaChainCheck : Bool :=
  rawChainOK 136 (omegaS.extract 0 10) omegaS (omegaBase.map Fin.val).toArray
      (wordsOf 10 omegaWords) 4 &&
    rawOrbitSizes 136 omegaS (omegaBase.map Fin.val).toArray == [136, 63, 30, 16, 8, 3, 2]

@[expose] def autChainCheck : Bool :=
  rawChainOK 136 (autS.extract 0 11) autS (autBase.map Fin.val).toArray (wordsOf 11 autWords) 4 &&
    rawOrbitSizes 136 autS (autBase.map Fin.val).toArray == [136, 63, 30, 16, 6, 4, 2, 2]

@[expose] def sylowChainCheck : Bool :=
  rawChainOK 136 (sylowS.extract 0 6) sylowS (sylowBase.map Fin.val).toArray
      (wordsOf 6 sylowWords) 4 &&
    rawOrbitSizes 136 sylowS (sylowBase.map Fin.val).toArray == [64, 2, 8, 4, 2]

@[expose] def omegaW (w : List ℤ) : Array ℕ := wordA 136 omegaS (rawInvs 136 omegaS) w

@[expose] def autW (w : List ℤ) : Array ℕ := wordA 136 autS (rawInvs 136 autS) w

@[expose] def sylowW (w : List ℤ) : Array ℕ := wordA 136 sylowS (rawInvs 136 sylowS) w

@[expose] def conjArr (t u : Array ℕ) : Array ℕ := compA 136 (compA 136 t u) (invCand 136 t)

@[expose] def commArr (t u : Array ℕ) : Bool := eqA 136 (compA 136 t u) (compA 136 u t)

@[expose] def powArr (t : Array ℕ) : ℕ → Array ℕ
  | 0 => idA 136
  | k + 1 => compA 136 t (powArr t k)

@[expose] def rvPerm : List ℕ := [0, 1, 2, 3, 4, 6, 5, 7, 9, 8]

@[expose] def structureCheck : Bool :=
  (List.range 10).all fun i =>
    eqA 136 (conjArr genArrs[10]! genArrs[i]!) genArrs[rvPerm.getD i 0]!

@[expose] def stabIdx : List ℕ := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]

@[expose] def stabCheck : Bool :=
  stabIdx.all (fun j => decide (j < omegaS.size) && (omegaS[j]!)[0]! == 0) &&
    (List.range 135).all fun p => stabIdx.any fun j => (omegaS[j]!)[p + 1]! != p + 1

@[expose] def bfsTree : Array ℕ × Array ℕ × Array ℕ := Id.run do
  let mut par : Array ℕ := Array.replicate 136 0
  let mut lab : Array ℕ := Array.replicate 136 0
  let mut dep : Array ℕ := (Array.replicate 136 1000).set! 0 0
  let mut queue : Array ℕ := #[0]
  let mut h := 0
  for _ in [0:136] do
    if h < queue.size then
      let x := queue[h]!
      h := h + 1
      for l in [0:10] do
        let y := (genArrs[l]!)[x]!
        if y < 136 && dep[y]! == 1000 then
          dep := dep.set! y (dep[x]! + 1)
          par := par.set! y x
          lab := lab.set! y l
          queue := queue.push y
  return (par, lab, dep)

@[expose] def treeOK (par lab dep : Array ℕ) : Bool :=
  dep[0]! == 0 &&
    (List.range 135).all fun i =>
      decide (par[i + 1]! < 136) && decide (lab[i + 1]! < 10) &&
        decide (dep[par[i + 1]!]! < dep[i + 1]!) && (genArrs[lab[i + 1]!]!)[par[i + 1]!]! == i + 1

@[expose] def treeCheck : Bool := treeOK bfsTree.1 bfsTree.2.1 bfsTree.2.2

@[expose] def sylowTables : List (List Table) :=
  chainTables 136 sylowS (sylowBase.map Fin.val).toArray

@[expose] def sylowGensT : Array Table := sylowGens.map (arrTable 136)

@[expose] def sylowGensInvT : Array Table := sylowGens.map fun t => arrTable 136 (invCand 136 t)

@[expose] def invList : List Table := filterProducts 136 (ordTest 136 2) sylowTables (idT 136) []

@[expose] def fourList : List Table := filterProducts 136 (ordTest 136 4) sylowTables (idT 136) []

@[expose] def repWords : List (List ℤ) :=
  [[6], [3], [4], [7, 3, 8], [7, 3, 8, 6], [8], [9], [2], [2, 6], [2, 7, 3, 8],
   [1, 7, 1, 2, 1, 7, 1, 2, 7, 3], [1, 7, 1, 2, 1, 7, 1, 2, 7, 3, 6], [1, 7, 1, 2, 1, 7, 1, 2, 7],
   [1, 7, 1, 2, 1, 7, 1, 2, 4, 8], [1, 8, 7, 1, 7, 8], [1, 8, 7, 1, 7, 8, 6], [1, 8, 7, 1, 7],
   [1, 8, 7, 1, 7, 8, 9], [1], [1, 6], [1, 3], [1, 4], [7, 1, 2, 1, 7, 1, 2, 7, 3], [1, 2, 1, 2],
   [1, 2, 1, 2, 6], [1, 2, 1, 2, 8], [1, 2, 1, 2, 9], [1, 2, 1, 8], [1, 2, 1, 9],
   [7, 1, 8, 2, 1, 2, 7, 8], [7, 1, 8, 2, 1, 7, 8], [7, 1, 8, 2, 1, 7, 9], [9, 1, 8, 1, 8, 9],
   [9, 1, 8, 1, 7, 3, 9], [8, 1, 9, 1, 8, 9], [8, 1, 9, 1, 7, 3, 9]]

@[expose] def repArrs : List (Array ℕ) := repWords.map sylowW

@[expose] def repTypes : List ℕ :=
  [3, 1, 1, 0, 4, 1, 1, 0, 4, 1, 0, 4, 2, 2, 0, 4, 2, 2, 0, 4, 2, 2, 1, 0, 4, 2, 2, 2, 2, 1, 2, 2,
   1, 2, 1, 2]

@[expose] def mainWords : List (List ℤ) :=
  [[1, 7, 1, 2, 1, 7, 1, 2, 7, 3], [9, 1, 8, 1, 8, 9], [9, 1, 8, 1, 7, 3, 9], [6],
   [1, 7, 1, 2, 1, 7, 1, 2, 7, 3, 6]]

@[expose] def mainArrs : List (Array ℕ) := mainWords.map sylowW

@[expose] def conjWords : List (List ℤ) :=
  [[], [3, 4, 1, 2], [10, 6, 8, 3, 4, 1, 2], [1, 3, 2, 4], [1, 3, 2, 4], [1, 2], [5, 10, 6, 1, 2],
   [5, 8, 1, 3, 2, 4], [5, 8, 1, 3, 2, 4], [8, 6, 1, 2], [], [], [3, 4, 3, 1, 2, 1],
   [10, 3, 6, 8, 4, 3, 1, 2], [3, 4], [3, 4], [1, 2, 1], [10, 6, 8, 1, 2], [3, 5, 4, 8, 3, 4],
   [3, 5, 4, 8, 3, 4], [3, 5, 4, 8, 1, 2, 1], [3, 7, 4, 10, 1, 2], [3, 4, 8, 3, 6], [5, 8, 3, 4],
   [5, 8, 3, 4], [5, 8, 1, 2, 1], [7, 10, 1, 2], [5, 8, 1, 2], [7, 10, 1, 2, 1], [8, 6], [8, 1],
   [5, 10], [], [], [5, 10, 6], [8, 7, 9]]

@[expose] def conjArrs : List (Array ℕ) := conjWords.map autW

@[expose] def sylowRepsCheck : Bool :=
  repsOK 136 sylowGensT sylowGensInvT invList (repArrs.map (arrTable 136)) 100 &&
    repArrs.all (fun r => ordTest 136 2 (arrTable 136 r)) &&
    (List.range 36).all fun j =>
      siftA 136 (rawLevels 136 omegaS (omegaBase.map Fin.val).toArray)
          (omegaBase.map Fin.val).toArray 0 (repArrs.getD j #[]) ==
        decide (repTypes.getD j 0 < 3) &&
      eqA 136 (conjArr (conjArrs.getD j #[]) (mainArrs.getD (repTypes.getD j 0) #[]))
        (repArrs.getD j #[])

@[expose] def cent0Words : List (List (List ℤ)) :=
  [[[10, 17, 1, 16, 4, 8, 5, 13, 14], [7, 3, 2, 1, 8, 3, 11, 5], [2, 4, 2, 4, 17, 16]],
    [[5, 1, 3, 1, 4, 3, 15, 11, 12], [8], [1, 11, 6, 3, 1, 4, 8, 3, 13, 15, 4, 5, 12],
     [1, 12, 3, 1, 8]],
    [[2, 4, 2, 17, 11, 5, 16, 12], [11, 6, 3, 1, 3, 11, 13, 12], [4, 5],
     [12, 11, 1, 4, 3, 12, 7, 13, 12]],
    [[2, 15, 2, 1, 15, 17, 8, 15, 17, 11], [15, 4, 2, 1, 4, 8, 17, 11, 16, 12, 18],
     [3, 2, 1, 12, 15, 3, 15, 16, 11, 15, 11, 5, 16], [4, 3, 2, 1, 12, 15, 3, 4, 17, 11]],
    [[2, 3, 16, 12], [3], [2, 3], [12, 3, 1, 3, 12]]]

@[expose] def cent0Check : Bool :=
  (List.range 5).all fun i =>
    (cent0Words.getD i []).all fun w => commArr (omegaW w) (mainArrs.getD i #[])

@[expose] def repGens (j : ℕ) : List (Array ℕ) :=
  (cent0Words.getD (repTypes.getD j 0) []).map (fun w => conjArr (conjArrs.getD j #[]) (omegaW w))
    ++ [repArrs.getD j #[]]

@[expose] def fiveOK (GT GI : Array Table) (b : Table)
    (c : Array Table × Array ℕ × Array ℕ) : Bool :=
  conjTreeOK 136 GT GI b c.1 c.2.1 c.2.2 && hkeysDistinct 136 c.1.toList && decide (5 ≤ c.1.size)

@[expose] def closureCheckAt (j : ℕ) : Bool :=
  let GT := ((repGens j).map (arrTable 136)).toArray
  let GI := ((repGens j).map fun t => arrTable 136 (invCand 136 t)).toArray
  let y := arrTable 136 (repArrs.getD j #[])
  fourList.all fun b => !commT 136 b y || fiveOK GT GI b (conjClosureH 136 GT GI b 5)

@[expose] def closureCheck : Bool := (List.range 36).all closureCheckAt

@[expose] def fgWords : List (List ℤ) := [[17, 13, 1, 11, 5], [3, 17, 11, 15, 17]]

@[expose] def fgCheck : Bool :=
  (List.range 2).all fun i =>
    let x := mainArrs.getD (i + 3) #[]
    let l := omegaW (fgWords.getD i [])
    let v := compA 136 (conjArr l x) x
    eqA 136 (compA 136 v v) (idA 136) && !eqA 136 v (idA 136)

@[expose] def oddData : List (List ℤ × List ℤ × ℕ × ℕ × ℕ) :=
  [([10, 1, 11, 1, 9, 11], [10, 2, 17, 1, 4, 17, 11, 5, 13, 12, -14], 15, 3, 3),
   ([8, 2, 17, 1, 12, 15, 3, 17, 15, 11], [2, 4, 2, 11, 15, 3, 16, 11, 15, 17, 11, 5, 16], 5, 5,
    3),
   ([18, 4, 13, 3, 2, 1, 17, 11, 15, 17, 6, 13, 12], [2, 4, 2, 3, 17, 11, 12], 3, 3, 3)]

@[expose] def oddCheck : Bool :=
  (List.range 3).all fun i =>
    let d := oddData.getD i ([], [], 0, 0, 0)
    let x := mainArrs.getD i #[]
    let u := omegaW d.1
    let v := omegaW d.2.1
    d.2.2.2.1 % 2 == 1 && d.2.2.2.2 % 2 == 1 &&
      ordTest 136 d.2.2.2.1 (arrTable 136 u) && ordTest 136 d.2.2.2.2 (arrTable 136 v) &&
      commArr u x && commArr v x && eqA 136 (powArr (compA 136 u v) d.2.2.1) x

@[expose] def invsCheck : Bool :=
  (List.range 36).all (fun j => (repGens j).all fun t => isInvA 136 t (invCand 136 t)) &&
    (conjArrs ++ mainArrs ++ repArrs).all (fun t => isInvA 136 t (invCand 136 t)) &&
    cent0Words.all (fun ws => ws.all fun w => isInvA 136 (omegaW w) (invCand 136 (omegaW w))) &&
    fgWords.all fun w => isInvA 136 (omegaW w) (invCand 136 (omegaW w))

end CFSG.EvenSmallLie.OmegaEightMinus
