module

public import CFSG.Monster.B.Fischer.InducedData
public import CFSG.Sporadic.Schreier.RuDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeHexA
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeHexB
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeHexC

public noncomputable section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.Sporadic.RuSchreier

@[expose] def ruThreeHex : String := ruThreeHexA ++ ruThreeHexB ++ ruThreeHexC

@[expose] def ruThreeArrs : Array (Array ℕ) :=
  #[ruArr4060 0, ruArr4060 1] ++ Array.ofFn (n := 9) fun j =>
    CFSG.Monster.B.Fischer.hexTable3 4060 (4060 * j.val) ruThreeHex

@[expose] def ruThreeWords : Array (List ℤ) :=
  #[[], [], [-2, -2], [-1, -3, -1, -3, -1, -3, -1, 3, 1, 3, 1, 3, 1, 2],
    [-1, -2, -1, -4, -2, -1, 2, 1, 2, 4, 1, 2, 1], [-4, 5, -4, -5], [-3, -4, 5, 4, 3],
    [-6, -6, 7, -6, 7, -6], [-6, -7, 8, 6, 8, 6], [-7, -7, -6, -7, 8, 7], [-4, -9, 6, 7, 3]]

@[expose] def ruThreeBase : List (Fin 4060) := [0, 978, 1914, 1524, 1, 479, 3650]

@[expose] def ruThreeRels : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 1), (0, 0, 2), (1, 1, 1), (1, 1, 2), (2, 2, 1), (2, 2, 2), (3, 3, 1), (3, 3, 2),
   (4, 5, 1), (4, 6, 2), (5, 6, 1), (5, 4, 2), (6, 4, 1), (6, 5, 2)]

@[expose] def ruThreeEval (w : List ℤ) : Array ℕ :=
  wordA 4060 ruThreeArrs (rawInvs 4060 ruThreeArrs) w

@[expose] def ruThreeQGens : Array (Array ℕ) :=
  #[ruThreeEval [-9], ruThreeEval [10, 11, 4, 3, 7, 6, -10, 8, 9]]

@[expose] def ruThreeLineWords : List (List ℤ) :=
  [[-9], [10, 11, 4, 3, 7, 6, -10, 8, 9], [3, 5, 9, 3, -8, 6, 7, 6, -9, 8],
   [-5, 11, 5, -11, -9, 6, 6, 10, 8], [6, 5, 11, 4, -9, 10, -7, 6, 10, 8],
   [-5, 11, 5, -11, -9, 6, 6, 10, 8, -9], [10, 11, 4, 3, 7, 6, -10, 8],
   [10, 11, 4, 3, 7, 6, -10, 8, -9], [3, 5, 9, 3, -8, 6, 7, 6, -9, 8, 9],
   [-10, 4, 5, 11, 6, 10, -9], [3, 5, 9, 3, -8, 6, 7, 6, -9, 8, -9],
   [6, 3, -7, 4, 11, 10, -7, -9, 8], [-4, 10, -5, -11, -8, -7, 6, -10, 9]]

@[expose] def ruThreeTransWords : List (List ℤ) :=
  [[], [-10, 5, -10, 6, 6, -10], [-8, -5, -7, 10, 11, -9, 8], [-7, -4, 5, 10, -6, 10, 8],
   [-6, 10, 5, -9, -7, -10], [4, -9, 4, -9, 8, 6, 10, 8], [9, 8, 5, 7, 8, 6, 10],
   [-10, 11, -4, -6, -8], [5, 10, 4, -8, -11, 10], [10, 9, 5, -10, 6, 6, 8],
   [11, 9, 4, -6, 7, -10, 8], [8, 5, 7, 8, 6, -9, 8], [-6, -4, 9, 7, -8]]

@[expose] def ruThreeLines : Array (Array ℕ) := (ruThreeLineWords.map ruThreeEval).toArray

@[expose] def ruThreeTransporters : Array (Array ℕ) := (ruThreeTransWords.map ruThreeEval).toArray

@[expose] def ruThreeRec : List ℕ := List.replicate 13 0

@[expose] def ruThreeC0Gens : Array (Array ℕ) :=
  #[ruThreeLines[0]!, ruThreeEval [-5, 11, 5, -7, 6, -11, 9],
    ruThreeEval [2, -10, -5, 2, 1, -4, -11, -9, 3, 10, 7, 7, -8, 9]]

@[expose] def ruThreeM : Array (Array ℕ) :=
  #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
    #[0, 1, 10, 8, 5, 4, 9, 7, 3, 6, 2],
    #[0, 2, 6, 1, 8, 9, 5, 3, 4, 10, 7]]

@[expose] def ruThreeM11 : Array (Array ℕ) :=
  #[#[0, 9, 2, 10, 6, 5, 4, 8, 7, 1, 3],
    #[3, 4, 7, 2, 5, 8, 6, 0, 1, 9, 10]]

end CFSG.EvenSporadicStandard.RuStd.S2
