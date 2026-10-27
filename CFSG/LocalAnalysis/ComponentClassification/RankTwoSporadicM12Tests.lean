module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2Exc
public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.RankThree.PartOne.KS.PKitLines

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M12

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.RankThree.PartOne CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def m12A1Arr : Array ℕ :=
  #[3, 1, 9, 0, 10, 11, 6, 7, 8, 2, 4, 5, 15, 13, 21, 12, 22, 23, 18, 19, 20, 14, 16, 17]

@[expose] def m12B1Arr : Array ℕ :=
  #[7, 2, 3, 1, 11, 9, 5, 8, 0, 6, 4, 10, 17, 20, 13, 12, 19, 15, 22, 21, 14, 16, 23, 18]

@[expose] def m12SigArr : Array ℕ :=
  #[12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

@[expose] def m12Base : List (Fin 24) := [0, 1, 2, 3, 4]

@[expose] def m12BaseArr : Array ℕ := (m12Base.map Fin.val).toArray

@[expose] def m12InP (S : Array (Array ℕ)) (t : Array ℕ) : Bool :=
  siftA 24 (rawLevels 24 S m12BaseArr) m12BaseArr 0 t

@[expose] def m12InR (S : Array (Array ℕ)) (t : Array ℕ) : Bool :=
  m12InP S t || m12InP S (compA 24 m12SigArr t)

@[expose] def m12PS : List ℕ := [0, 1, 2, 3, 4, 12, 13, 14, 15, 16]

@[expose] def m12Fuel : ℕ := 2 ^ 16

theorem m12PS_lt : ∀ p ∈ m12PS, p < 24 := by decide

@[expose] def rdExcA (tk : Array ℕ) (n : ℕ) (p : ℕ) : ExcRef × ℕ :=
  let a := rdArr tk n (p + 1)
  (⟨tk[p]!, a.1⟩, a.2)

@[expose] def decodeExcA (n : ℕ) (s : String) : List ExcRef :=
  (rdListC (decodeNats s) (rdExcA (decodeNats s) n) 0).1

@[expose] def m12Check (S : Array (Array ℕ)) (Wd : Array (List ℤ)) (e0 : Array (Array ℕ))
    (sc sx : String) : Bool :=
  let d := decodeCert 24 sc
  decide (2 ≤ S.size) && caseChainOK2P 24 S m12BaseArr Wd m12A1Arr m12B1Arr &&
    censusExcOK 24 m12PS m12Fuel (m12InP S) (m12InP S) (m12InR S) false false false d.sGens
      d.roots d.nodes e0 (decodeExcA 24 sx) &&
    (allLt d.sGens.size fun k =>
      m12InP S d.sGens[k]! || m12InP S (compA 24 m12SigArr d.sGens[k]!)) &&
    (enumBfs 24 d.sGens m12PS m12Fuel).pts.size == 128

end CFSG.ComponentClassification.RankTwoSporadic.M12
