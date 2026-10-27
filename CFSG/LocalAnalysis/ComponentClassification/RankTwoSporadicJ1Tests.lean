module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ1Full
public import CFSG.Sporadic.Schreier.J1CertData

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.J1

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def j1Gens : Array (Array ℕ) :=
  #[CFSG.Sporadic.Schreier.j1A1List.toArray, CFSG.Sporadic.Schreier.j1A2List.toArray]

@[expose] def j1PS : List ℕ := [0, 1, 2]

@[expose] def j1Fuel : ℕ := 2 ^ 20

theorem j1PS_lt : ∀ p ∈ j1PS, p < 3080 := by decide

@[expose] def j1Check (sc sp : String) : Bool :=
  let prog := decodePairs sp
  let regs := slpRegs 3080 j1Gens prog
  let idx := regIndex 3080 j1PS regs
  let d := decodeFCertR regs sc
  slpOK 3080 j1Gens prog &&
    fCensusOK 3080 j1PS j1Fuel (inRegs 3080 j1PS regs idx) j1Gens d.sGens d.nodes &&
    (allLt d.sGens.size fun k => inRegs 3080 j1PS regs idx d.sGens[k]!) &&
    (enumBfs 3080 d.sGens j1PS j1Fuel).pts.size == 8

end CFSG.ComponentClassification.RankTwoSporadic.J1
