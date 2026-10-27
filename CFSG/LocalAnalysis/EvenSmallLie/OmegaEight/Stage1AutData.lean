module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelData

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1.Model

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def aDeg : Eps → ℕ
  | .plus => 360
  | .minus => 136

@[expose] def qWordsPlus : List (List ℤ) :=
  [[2, 15, 11], [1, 10, 1, 10], [1, 11, 1, 11], [1, 9, 1, 9], [1, 3, 1, 3], [1]]

@[expose] def qtArr : Eps → ℕ → Array ℕ
  | .plus, j => OmegaEight.omegaW (qWordsPlus.getD j [])
  | .minus, j => psiArr .minus (2 ^ j)

@[expose] def psiTArr (ε : Eps) (y : ℕ) : Array ℕ :=
  (List.range 6).foldl
    (fun acc j => if y.testBit j then compA (aDeg ε) acc (qtArr ε j) else acc) (idA (aDeg ε))

@[expose] def psiTTabPlus : Array (Array ℕ) := Array.ofFn (n := 64) fun y => psiTArr .plus y.val

@[expose] def psiTTabMinus : Array (Array ℕ) := Array.ofFn (n := 64) fun y => psiTArr .minus y.val

@[expose] def psiTT (ε : Eps) (y : ℕ) : Array ℕ :=
  (match ε with
    | .plus => psiTTabPlus
    | .minus => psiTTabMinus).getD y #[]

@[expose] def aWordsMinus : List (List ℤ) :=
  [[-3, 5, 3], [-7, 12, 6], [-13, -6, -13, -3, 6, 3], [-11, -5, -10, 6, 8], [-3, -4, 8, 4, 3],
    [-13, -16, -13, -1, -13, 16, 2], [-4, 17, 4], [-12, -18, -16, -12, -17, 16, 17, 12, 16]]

@[expose] def aSMinus : Array (Array ℕ) :=
  OmegaEight.pushWords 136 OmegaEightMinus.genArrs aWordsMinus

@[expose] def aS : Eps → Array (Array ℕ)
  | .plus => OmegaEight.autS
  | .minus => aSMinus

@[expose] def aK : Eps → ℕ
  | .plus => 10
  | .minus => 11

@[expose] def aWords : Eps → List (List ℤ)
  | .plus => OmegaEight.autWords
  | .minus => aWordsMinus

@[expose] def aBase : (ε : Eps) → List (Fin (aDeg ε))
  | .plus => ([0, 2, 1, 4, 32, 16, 17] : List (Fin 360))
  | .minus => ([0, 2, 1, 16, 72, 8, 36] : List (Fin 136))

@[expose] def aBaseA (ε : Eps) : Array ℕ := ((aBase ε).map Fin.val).toArray

@[expose] def aSizes : Eps → List ℕ
  | .plus => [360, 63, 30, 12, 8, 4, 4]
  | .minus => [136, 63, 30, 16, 12, 4, 2]

@[expose] def aLevelsPlus : Array Level := rawLevels 360 OmegaEight.autS (aBaseA .plus)

@[expose] def aLevelsMinus : Array Level := rawLevels 136 aSMinus (aBaseA .minus)

@[expose] def aLevels : Eps → Array Level
  | .plus => aLevelsPlus
  | .minus => aLevelsMinus

@[expose] def memA (ε : Eps) (g : Array ℕ) : Bool := siftA (aDeg ε) (aLevels ε) (aBaseA ε) 0 g

@[expose] def omLevelsPlus : Array Level :=
  rawLevels 360 OmegaEight.omegaS ((OmegaEight.omegaBase.map Fin.val).toArray)

@[expose] def memOmPlus (g : Array ℕ) : Bool :=
  siftA 360 omLevelsPlus ((OmegaEight.omegaBase.map Fin.val).toArray) 0 g

@[expose] def inR (ε : Eps) (z : ℕ) : Bool := allLt 63 fun y => (psiTT ε (y + 1))[z]! != z

@[expose] def autCheck (ε : Eps) : Bool :=
  let n := aDeg ε
  rawChainOK n ((aS ε).extract 0 (aK ε)) (aS ε) (aBaseA ε) (OmegaEight.wordsOf (aK ε) (aWords ε))
      4 &&
    rawOrbitSizes n (aS ε) (aBaseA ε) == aSizes ε &&
    allLt 64 (fun y => isInvA n (psiTT ε y) (invCand n (psiTT ε y)) && memA ε (psiTT ε y) &&
      (match ε with
        | .plus => memOmPlus (psiTT ε y) &&
            eqA 120 (OmegaEight.copy0Arr (psiTT ε y)) (psiArr .plus y)
        | .minus => eqA 136 (psiTT ε y) (psiArr .minus y))) &&
    allLt 64 (fun y => allLt 64 fun y' =>
      eqA n (psiTT ε (y ^^^ y')) (compA n (psiTT ε y) (psiTT ε y'))) &&
    (aBaseA ε).all (inR ε) &&
    allLt n (fun z => !(inR ε z) || (List.range 64).any fun y => (psiTT ε y)[0]! == z)

end CFSG.EvenSmallLie.OmegaEight.Stage1.Model
