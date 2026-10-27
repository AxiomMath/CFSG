module

public import CFSG.LieType.Multipliers.U43Data
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelU43Arr
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
public import CFSG.LieType.Multipliers.U43Action

public section

namespace CFSG.EvenSmallLie.Child3.SelU43

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.LieType.Multipliers.U43
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.J2Cover
open CFSG.EvenSmallLie.OmegaEight (pushWords wordsOf)

@[expose] def deltaArr : Array ℕ :=
  Array.ofFn (n := 820) fun j =>
    ptIndex fun k => if k = 0 then (⟨0, 1⟩ : F9) * decode j.val k else decode j.val k

@[expose] def sigmaArr : Array ℕ :=
  Array.ofFn (n := 820) fun j => ptIndex fun k => decode j.val k * decode j.val k * decode j.val k

@[expose] def autGens : Array (Array ℕ) := #[tabA, tabB, deltaArr, sigmaArr]

@[expose] def autWords : List (List ℤ) :=
    [[-4, 3, 3], [-1, -2, 3, 2, 1], [6, -4, 6, 4, -6], [-3, -6, -4, 7, -1, -6, 5, -2],
     [-8, 7, 8], [-5, -6, -4, 9, 6]]

@[expose] def autS : Array (Array ℕ) := pushWords 820 autGens autWords

@[expose] def autBase : List (Fin 820) := [0, 1, 3, 81, 9]

@[expose] def sylowGenWords : List (List ℤ) :=
    [[-2, 7, 2, 1, 9, 6, 8, 6, 5, -10, 8, 9], [4, -6, 4, 1, 5, -6, 4, 6, 9, 10, -9],
     [2, 2, 2, 4, 5, 8, 7, -9], [5, -2, -2, -6, 9, -6, -3, 5, -9, 10, 9]]

@[expose] def autW (w : List ℤ) : Array ℕ := wordA 820 autS (rawInvs 820 autS) w

@[expose] def sylowGens : Array (Array ℕ) := (sylowGenWords.map autW).toArray

@[expose] def sylowWords : List (List ℤ) := [[-3, 4, 2, 4, 2], [-2, -5, -4, 5, 1]]

@[expose] def sylowS : Array (Array ℕ) := pushWords 820 sylowGens sylowWords

@[expose] def sylowBase : List (Fin 820) := [0, 1]

@[expose] def autChainCheck : Bool :=
  rawChainOK 820 (autS.extract 0 4) autS (autBase.map Fin.val).toArray (wordsOf 4 autWords) 4 &&
    rawOrbitSizes 820 autS (autBase.map Fin.val).toArray == [540, 252, 2, 24, 4]

@[expose] def sylowChainCheck : Bool :=
  sylowGenWords.all (lettersOK autS.size) &&
    rawChainOK 820 (sylowS.extract 0 4) sylowS (sylowBase.map Fin.val).toArray
      (wordsOf 4 sylowWords) 4 &&
    rawOrbitSizes 820 sylowS (sylowBase.map Fin.val).toArray == [256, 4]

@[expose] def tChainCheck : Bool :=
  rawChainOK 820 (chainS.extract 0 2) chainS (chainBase.map Fin.val).toArray chainW 4 &&
    rawOrbitSizes 820 chainS (chainBase.map Fin.val).toArray == [540, 252, 24]

@[expose] def normCheck : Bool :=
  [deltaArr, sigmaArr].all fun g => isInvA 820 g (invCand 820 g) &&
    [tabA, tabB].all fun x =>
      siftA 820 (rawLevels 820 chainS (chainBase.map Fin.val).toArray)
        (chainBase.map Fin.val).toArray 0 (conjA 820 g x)

@[expose] def u43Roots : List (ℕ × List (List ℤ)) :=
    [(0, [[3], [4], [5], [6], [7]]),
     (4, [[-1, -5, -2, -1, 3, 1, 2, 5, 1], [-1, 2, 7, -3, 4, 2, 3]])]

@[expose] def centCheck : Bool := centOK 820 chainS u43Roots

@[expose] def sylowW (w : List ℤ) : Array ℕ := wordA 820 sylowS (rawInvs 820 sylowS) w

@[expose] def tW (w : List ℤ) : Array ℕ := wordA 820 chainS (rawInvs 820 chainS) w

@[expose] def sylowTables : List (List Table) :=
  chainTables 820 sylowS (sylowBase.map Fin.val).toArray

@[expose] def sylowGensT : Array Table := sylowGens.map (arrTable 820)

@[expose] def sylowGensInvT : Array Table := sylowGens.map fun t => arrTable 820 (invCand 820 t)

@[expose] def invList : List Table := filterProducts 820 (ordTest 820 2) sylowTables (idT 820) []

@[expose] def repWords : List (List ℤ) :=
    [[1], [2], [3], [2, 1], [3, 1], [3, 2, 3, 2], [3, 5], [-4, 2, 3, 1, 6, 5], [4, 4, 4, 4],
     [3, 2, 3, 2, 1], [3, 4, 3, 2, 1], [3, 4, 6, 2, 5], [4, 3, 2, 3, 6], [-4, -4, 5, 2, 5],
     [5], [-4, 3, 4, 4, 6, 5], [2, 4, 1, 5], [4, 5, 3, 2, 6], [1, 5, 1, 5]]

@[expose] def repArrs : List (Array ℕ) := repWords.map sylowW

@[expose] def witWords : List (List ℤ) :=
    [[-6, 7, 2, 1, -6, 4, 5, 6, -7, 6], [6, -7, 1, -7, -3, 5, -7, 6, 7],
     [4, 1, 7, 2, -5, -6, 4, 3, 7], [-2, 1, 5, 2, -4, 3, -5, -7, 6, 7],
     [-7, 2, 2, 1, 3, -4, 6, 3, -7, -6], [3, 1, 2, -7, -3, 6, 7],
     [-5, -4, 2, -3, -4, 3, 6, 7, 6], [5, -4, 2, -3, -4, -3, 6, -7],
     [2, -7, -2, -4, -3, -7, 4, 7, 6], [4, 7, 4, 1, 6, -7, 4, -6, 7, -6],
     [7, 1, -3, 1, 6, 7, 5, -6, -7, 6], [2, 3, -5, 1, -6, -5, -6, 7, 6],
     [-5, 4, 2, 4, 3, -5, 3, -6, -7], [2, 6, -5, 1, -4, 3, -5, 6, -7], [1, -5, 2, 3, 7, 5, 7],
     [-5, 4, 1, 5, -4, -6, 3, 6, -7], [6, 4, 2, 1, -4, -3, -6, 7, -6],
     [-2, 5, 4, 1, 5, -3, -4, 3, 7, -6, 7], [1, -2, 5, 1, -7, 5, 3, 7]]

@[expose] def repsCheck : Bool :=
  repsOK 820 sylowGensT sylowGensInvT invList (repArrs.map (arrTable 820)) 100 &&
    repArrs.all fun r => ordTest 820 2 (arrTable 820 r)

@[expose] def witCheck : Bool :=
  repWords.all (lettersOK sylowS.size) && witWords.all (lettersOK chainS.size) &&
    repWords.length == 19 && witWords.length == 19 &&
    (List.range 19).all fun j => witOK 820 (repArrs.getD j #[]) (tW (witWords.getD j []))

end CFSG.EvenSmallLie.Child3.SelU43
