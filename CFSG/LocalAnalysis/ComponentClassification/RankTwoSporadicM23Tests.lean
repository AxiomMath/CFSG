module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSLP
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM24Tests

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M23

open CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def m23Gens : Array (Array ℕ) :=
  #[#[1, 0, 3, 2, 4, 5, 7, 6, 9, 8, 10, 11, 13, 12, 15, 14, 16, 17, 19, 18, 21, 20, 22],
    #[15, 8, 0, 4, 7, 21, 6, 22, 20, 9, 2, 1, 19, 17, 16, 10, 14, 5, 18, 12, 11, 13, 3]]

@[expose] def m23PS : List ℕ := [0, 1, 2, 3, 4, 5, 6]

@[expose] def m23Fuel : ℕ := 2 ^ 20

theorem m23PS_lt : ∀ p ∈ m23PS, p < 23 := by decide

@[expose] def m23Check (sc sp : String) : Bool :=
  let prog := decodePairs sp
  let regs := slpRegs 23 m23Gens prog
  let idx := regIndex 23 m23PS regs
  let d := decodeCert 23 sc
  slpOK 23 m23Gens prog &&
    censusOK 23 m23PS m23Fuel (inRegs 23 m23PS regs idx) M24.allA true false false d.sGens
      d.roots d.nodes &&
    (allLt d.sGens.size fun k => inRegs 23 m23PS regs idx d.sGens[k]!) &&
    (enumBfs 23 d.sGens m23PS m23Fuel).pts.size == 128

end CFSG.ComponentClassification.RankTwoSporadic.M23
