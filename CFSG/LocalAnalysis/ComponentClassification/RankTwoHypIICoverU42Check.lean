module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheck
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.ComponentClassification.RankTwoHypIICover.U42

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.ComponentClassification.CatFactsSmall.PSp43

@[expose] def arr45 (g : Equiv.Perm (Fin 45)) : Array ℕ := Array.ofFn fun i : Fin 45 => (g i).val

@[expose] def u42Gens : Array (Array ℕ) := #[arr45 x45, arr45 y45]

@[expose] def u42Words : List (List ℤ) :=
  [[2, 2, -1, 2, -1, 2, -2, 1, 2, 1, 1, -1, -2],
    [-1, 3, 2, -1, -2, -2, 2, 1, 2, 2, -2, -2, -2, 2, 2, 2, 1, -2, 1, -2, 2, 2, 1, -2, -1, 1, -2,
      -1],
    [3, -4, -1, -1, 1, 1, -2, -1, 2],
    [5, -4, 3, 4, 2, -4, 2, -1, 2, -2, 1, -1, 1, 1, -1, 2, 1]]

@[expose] def u42S : Array (Array ℕ) :=
  CFSG.EvenSmallLie.OmegaEight.pushWords 45 u42Gens u42Words

@[expose] def u42BaseL : List (Fin 45) := [1, 0, 16, 3]

@[expose] def u42Base : Array ℕ := (u42BaseL.map Fin.val).toArray

@[expose] def u42InX (t : Array ℕ) : Bool := siftA 45 (rawLevels 45 u42S u42Base) u42Base 0 t

@[expose] def u42PS : List ℕ := [0, 1, 16, 3, 2, 4, 5, 6, 7]

@[expose] def u42Fuel : ℕ := 2 ^ 12

theorem u42PS_lt : ∀ p ∈ u42PS, p < 45 := by decide

@[expose] def u42Check (sc : String) : Bool :=
  let d := decodeCert 45 sc
  rawChainOK 45 (u42S.extract 0 2) u42S u42Base
      (CFSG.EvenSmallLie.OmegaEight.wordsOf 2 u42Words) 4 &&
    censusOK 45 u42PS u42Fuel u42InX u42InX false true false d.sGens d.roots d.nodes &&
    (allLt d.sGens.size fun k =>
      u42InX d.sGens[k]! || u42InX (compA 45 (arr45 f45) d.sGens[k]!)) &&
    (enumBfs 45 d.sGens u42PS u42Fuel).pts.size == 128

end CFSG.ComponentClassification.RankTwoHypIICover.U42
