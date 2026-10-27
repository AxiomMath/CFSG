module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRuConj
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDecodeR
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzData
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSLP
public import CFSG.Sporadic.SuzOddCore.SmallChainCheckInputs

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Suz

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.SuzOddCore

@[expose] def suzInM (t : Array ℕ) : Bool := siftA 1782 smallLevels smallBaseNat.toArray 0 t

@[expose] def suzInT (t : Array ℕ) : Bool := suzInM t || suzInM (compA 1782 vArr t)

@[expose] def suzGensR : Array (Array ℕ) := smallStrongArrs.push vArr

@[expose] def suzPS : List ℕ := [0, 1, 2, 3, 4, 8]

@[expose] def suzFuel : ℕ := 2 ^ 20

theorem suzPS_lt : ∀ p ∈ suzPS, p < 1782 := by decide

@[expose] def suzE0 : Array (Array ℕ) :=
  #[hexTable 3 1782 0 suzE0Text, hexTable 3 1782 1782 suzE0Text]

@[expose] def suzGensOK (gs : Array (Array ℕ)) : Bool :=
  allLt gs.size fun k => suzInM gs[k]! || suzInM (compA 1782 vArr gs[k]!)

@[expose] def suzCheckII (sc sp : String) : Bool :=
  let d := decodeCertR (slpRegs 1782 suzGensR (decodePairs sp)) sc
  conjCensusOK 1782 suzPS suzFuel suzInM suzInM suzInT false true false d.sGens d.roots d.nodes
      #[] [] &&
    suzGensOK d.sGens && (enumBfs 1782 d.sGens suzPS suzFuel).pts.size == 16384

@[expose] def suzCheckExc (e0 : Array (Array ℕ)) (sc sx sp : String) : Bool :=
  let regs := slpRegs 1782 suzGensR (decodePairs sp)
  let d := decodeCertR regs sc
  conjCensusOK 1782 suzPS suzFuel suzInM suzInM suzInT false false false d.sGens d.roots d.nodes
      e0 (decodeExcR regs sx) &&
    suzGensOK d.sGens && (enumBfs 1782 d.sGens suzPS suzFuel).pts.size == 16384

end CFSG.ComponentClassification.RankTwoSporadic.Suz
