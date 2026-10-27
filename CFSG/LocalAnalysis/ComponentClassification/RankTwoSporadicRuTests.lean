module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRuConj
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDecodeR
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRuData
public import CFSG.Sporadic.Schreier.RuCheckChainsInputs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSLP

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Ru

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.RuSchreier

@[expose] def ruInP (t : Array ℕ) : Bool :=
  siftA 4060 (rawLevels 4060 (ruField4060 3) (ruBaseArr 4060 ruJoinBase))
    (ruBaseArr 4060 ruJoinBase) 0 t

@[expose] def ruGensR : Array (Array ℕ) := ruField4060 3

@[expose] def ruPS : List ℕ := [0, 1, 2, 3]

@[expose] def ruFuel : ℕ := 2 ^ 20

theorem ruPS_lt : ∀ p ∈ ruPS, p < 4060 := by decide

@[expose] def ruE0 : Array (Array ℕ) := #[ruA0A, ruHexRow ruE0RText.toUTF8 4060 0]

@[expose] def ruGensOK (gs : Array (Array ℕ)) : Bool :=
  allLt gs.size fun k => ruInP gs[k]! || ruInP (compA 4060 (idA 4060) gs[k]!)

@[expose] def ruCheckExc (e0 : Array (Array ℕ)) (sc sx sp : String) : Bool :=
  let regs := slpRegs 4060 ruGensR (decodePairs sp)
  let d := decodeCertR regs sc
  conjCensusOK 4060 ruPS ruFuel ruInP ruInP (fun a => ruInP a || ruInP (compA 4060 (idA 4060) a))
      false false false d.sGens d.roots d.nodes e0 (decodeExcR regs sx) &&
    ruGensOK d.sGens && (enumBfs 4060 d.sGens ruPS ruFuel).pts.size == 16384

end CFSG.ComponentClassification.RankTwoSporadic.Ru
