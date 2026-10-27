module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM22Tests

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M24

open CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.ComponentClassification.RankTwoSporadic.M22
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def allA (_ : Array ℕ) : Bool := true

@[expose] def m24Check (s : String) : Bool :=
  let d := decodeCert 24 s
  censusOK 24 m22PS m22Fuel autA allA true false true d.sGens d.roots d.nodes &&
    (allLt d.sGens.size fun k => autA d.sGens[k]!) &&
    (enumBfs 24 d.sGens m22PS m22Fuel).pts.size == 1024

end CFSG.ComponentClassification.RankTwoSporadic.M24
