module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDecodeR
public import CFSG.Sporadic.SmallOddCore.J3Data
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSLP
public import CFSG.Sporadic.Schreier.PairJ3CheckInputs

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.J3

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.Sporadic.Schreier
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def j3InP (t : Array ℕ) : Bool :=
  siftA 6156 (rawLevels 6156 j3StrongArrs PairJ3.baseArr) PairJ3.baseArr 0 t

@[expose] def j3UArr : Array ℕ :=
  CFSG.Sporadic.SmallOddCore.Native.natArr CFSG.Sporadic.SmallOddCore.j3OuterTbl

@[expose] def j3GensR : Array (Array ℕ) := j3StrongArrs.push j3UArr

@[expose] def j3PS : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7]

@[expose] def j3Fuel : ℕ := 2 ^ 20

theorem j3PS_lt : ∀ p ∈ j3PS, p < 6156 := by decide

@[expose] def j3Check (sc sp : String) : Bool :=
  let d := decodeCertR (slpRegs 6156 j3GensR (decodePairs sp)) sc
  isInvA 6156 j3UArr (invCand 6156 j3UArr) &&
    censusOK 6156 j3PS j3Fuel j3InP j3InP false false false d.sGens d.roots d.nodes &&
    (allLt d.sGens.size fun k =>
      j3InP d.sGens[k]! || j3InP (compA 6156 j3UArr d.sGens[k]!)) &&
    (CFSG.RankThree.Native.enumBfs 6156 d.sGens j3PS j3Fuel).pts.size == 256

end CFSG.ComponentClassification.RankTwoSporadic.J3
