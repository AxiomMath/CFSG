module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSLP
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDecodeR
public import Certificates.Data.CFSGNative.PSL3Four.Certificate

public section

namespace CFSG.ComponentClassification.RankTwoL3Four.HypII

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer

@[expose] def l34GensR : Array (Array ℕ) := CFSG.PSL3Four.Native.gTabs

@[expose] def l34GensS : Array (Array ℕ) := CFSG.PSL3Four.Native.gensS

@[expose] def l34PS : List ℕ := [0, 1, 5, 10, 3]

@[expose] def l34Fuel : ℕ := 2 ^ 20

theorem l34PS_lt : ∀ p ∈ l34PS, p < 42 := by decide

@[expose] def l34EnumS : ArrCert := enumBfs 42 l34GensS l34PS l34Fuel

@[expose] def l34InS (a : Array ℕ) : Bool := memA 42 l34EnumS a

@[expose] def l34CheckII (sc sp : String) : Bool :=
  let prog := decodePairs sp
  let regs := slpRegs 42 l34GensR prog
  let d := decodeCertR regs sc
  enumOK 42 l34GensS l34PS l34EnumS && slpOK 42 l34GensR prog &&
    censusOK 42 l34PS l34Fuel l34InS l34InS false true false d.sGens d.roots d.nodes &&
    (allLt d.sGens.size fun k => (List.range regs.size).any fun r => eqA 42 d.sGens[k]! regs[r]!) &&
    (enumBfs 42 d.sGens l34PS l34Fuel).pts.size == 256

end CFSG.ComponentClassification.RankTwoL3Four.HypII
