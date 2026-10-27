module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDecodeR
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSLP
public import CFSG.RankThree.Native.HSMcLSmallCheckInputs

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.HS

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def hsInP (t : Array ℕ) : Bool :=
  siftA 100 (rawLevels 100 hs100StrongArrs hs100BaseArr) hs100BaseArr 0 t

@[expose] def hsGensR : Array (Array ℕ) := #[hs100Arr 0, hs100Arr 1, hs100Arr 15]

@[expose] def hsPS : List ℕ := [0, 1, 2, 3, 4]

@[expose] def hsFuel : ℕ := 2 ^ 20

theorem hsPS_lt : ∀ p ∈ hsPS, p < 100 := by decide

@[expose] def hsCheck (allowPW allowInX : Bool) (sc sp : String) : Bool :=
  let d := decodeCertR (slpRegs 100 hsGensR (decodePairs sp)) sc
  censusOK 100 hsPS hsFuel hsInP hsInP allowPW allowInX false d.sGens d.roots d.nodes &&
    (allLt d.sGens.size fun k =>
      hsInP d.sGens[k]! || hsInP (compA 100 (hs100Arr 15) d.sGens[k]!)) &&
    (enumBfs 100 d.sGens hsPS hsFuel).pts.size == 1024

end CFSG.ComponentClassification.RankTwoSporadic.HS
