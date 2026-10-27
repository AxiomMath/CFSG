module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.FourCheck
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22Data
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22OuterData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Check
public import CFSG.Sporadic.Schreier.M22Data

public section

namespace CFSG.EvenSporadicStandard.HypOne.M22

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native

@[expose] def gensM : List (Equiv.Perm (Fin 22)) := [m22gA, m22gB]

@[expose] def gensA : List (Equiv.Perm (Fin 22)) := [m22gA, m22gB, m22Delta]

@[expose] def centGens1 : List (Equiv.Perm (Fin 22)) := m22CentWords1.map (evalCodes gensM)

@[expose] def innerFourWords : List (List ℤ) :=
  [[3, -2, -1, -1, 2], [-1, -2, -1, -2, 1, 2, -1, -1, 2], [-2, -1, 2, 1, 1, -3], [-3, 1, -3],
   [3, 2, 1, 1], [-2, -1, -2, 1, 1, 1]]

@[expose] def zWordA : List ℤ :=
  [3, 1, 2, 2, -3, -1, -2, -3, 2, -3, -2, -1, -2, -3, 2, -1, -2, -1, 2, 2, -1, -3, -2, -1, 2, -3,
    -2, -3, -2, -2, -3, 1, 3, 2, 2, 3, 2, 3, -2, 1, 2, 3, 1, -2]

@[expose] def kGensA : List (Equiv.Perm (Fin 22)) :=
  centGens1 ++ [evalCodes gensA zWordA]

@[expose] def kChainWordsA : List (List ℤ) :=
  [[-2, 4, 2], [-1, -1, 4, 3]]

@[expose] def kChainA : RawSchreierDatum 22 :=
  certificate (by decide) kGensA kChainWordsA
    #v[0, 1, 3, 2] (by decide)

@[expose] def kFourWordsA : List (List ℤ) :=
  [[1, 1], [-2, -1, -2, 1, 1], [3, -1, -3, 1, 4, -1, -4], [4, 3, -4, -2], [4, 1, -4, -1, -3, 2],
   [2, 1, 4, -3, -3, 4, 3], [1, 1, -4], [-2, -3, 4, 3], [4, -2, 1, 1, 1], [3, -1, 3, -4],
   [-1, -1, 3, 1, 4, -1], [4, -2, 1, 1, 1, -3]]

@[expose] def kGensO1 : List (Equiv.Perm (Fin 22)) :=
  m22OutCentWords1.map (evalCodes gensM) ++ [m22OutReps.getD 0 1]

@[expose] def kChainWordsO1 : List (List ℤ) :=
  [[-1, 3], [5, 2, -5], [-2, 5, 6, -5], [-5, -2, -5, -1, 4]]

@[expose] def kChainO1 : RawSchreierDatum 22 :=
  certificate (by decide) kGensO1 kChainWordsO1
    #v[0, 1, 2] (by decide)

@[expose] def kFourWordsO1 : List (List ℤ) :=
  [[-1, -3, -1, -2, 1], [-2, -1, -2, -3], [-3, 2, 1, 1], [1, -3, -1, -4, -3, 2, 4, 3],
   [-3, -4, -2, 3, 3, 1], [3, -1, -1, -1, -3, 2, 4, 3], [-3, -1, -1, -4], [4, 1, 1, 3]]

@[expose] def kGensO2 : List (Equiv.Perm (Fin 22)) :=
  m22OutCentWords2.map (evalCodes gensM) ++ [m22OutReps.getD 1 1]

@[expose] def kChainWordsO2 : List (List ℤ) :=
  [[-1, 4], [2, 5, 2, 5, 2], [-5, -6, -2, -2, 6, 2, 2]]

@[expose] def kChainO2 : RawSchreierDatum 22 :=
  certificate (by decide) kGensO2 kChainWordsO2
    #v[0, 1, 2, 3] (by decide)

@[expose] def kFourWordsO2 : List (List ℤ) :=
  [[4, 2, -3, 1, 3, -1, -2, -1, -2], [2, 1, 1, 1, -2, 1, 2], [-2], [-1, -1, 4, 1, 2, 1, 2, 1],
   [-1, 2, 1, 1, 1, -2, 1, 2, -3, -1, 3, -2, -4], [-1, 2, 1, 2, 1]]

@[expose] def wordE1 : List ℤ :=
  [2, 1, 2, -1, 2, -1, -2, -1, -1, 2, -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -2, 1, -2, 1]

@[expose] def wordE2 : List ℤ :=
  [-2, 1, -2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, -2, 1, 2, 2, 1, -2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1,
    2, -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -2, -1, -2, -1, -2, -2, -1, 2, -1, 2, -1, -2, -1,
    -2]

@[expose] def wordE3 : List ℤ :=
  [-1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -2, -1, 2, 2, 1, 2, 1, -2, 1, 2, 2, 1, -2, 1, -2, 1, 2,
    1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 2, 1, -2, 1, 2, -1, 2, -1, 2, -1, -2, -1,
    -2]

@[expose] def wordL1 : List ℤ :=
  [-1, 2, -1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -2, -1, -2, -1, 2,
    -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -1, 2, -1, -2, 1, -2, 1, 2, 1, 1, 2, 2, 1]

@[expose] def wordL2 : List ℤ :=
  [-1, -2, -2, -1, -1, -2, -1, -2, -1, -2, -1, -2, -2, -1, -1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1,
    -2, 1, -2, 1, 2, 1, 2, 2, -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2]

@[expose] def l1 : Equiv.Perm (Fin 22) := evalCodes gensM wordL1

@[expose] def l2 : Equiv.Perm (Fin 22) := evalCodes gensM wordL2

@[expose] def e1 : Equiv.Perm (Fin 22) := evalCodes gensM wordE1

@[expose] def e2 : Equiv.Perm (Fin 22) := evalCodes gensM wordE2

@[expose] def e3 : Equiv.Perm (Fin 22) := evalCodes gensM wordE3

@[expose] def innerData : Bool := fourCheck 22 m22CentQ1 centGens1 innerFourWords 4000

@[expose] def autData : Bool :=
  kChainA.check && kChainO1.check && kChainO2.check &&
    commT 22 (toTable (evalCodes gensA zWordA)) (toTable m22gA) &&
    m22Certificate.sift (evalCodes gensA zWordA) 0 == false &&
    fourCheck 22 kChainA kGensA kFourWordsA 4000 &&
    fourCheck 22 kChainO1 kGensO1 kFourWordsO1 4000 &&
    fourCheck 22 kChainO2 kGensO2 kFourWordsO2 4000

@[expose] def foursData : Bool :=
  ordTest 22 2 (toTable (l1 * m22OutReps.getD 0 1 * l1⁻¹ * (m22OutReps.getD 0 1)⁻¹)) &&
    ordTest 22 2 (toTable (l2 * m22OutReps.getD 1 1 * l2⁻¹ * (m22OutReps.getD 1 1)⁻¹))

@[expose] def e8Data : Bool := e8Check 22 (toTable e1) (toTable e2) (toTable e3)

end CFSG.EvenSporadicStandard.HypOne.M22
