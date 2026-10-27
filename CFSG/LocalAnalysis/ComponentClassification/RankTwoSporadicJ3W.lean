module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ3Tests
public import CFSG.Certificates.Kernel.Census.ToMainConj

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.J3

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.Sporadic.Schreier
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native
open CFSG.KC.Census

@[expose] noncomputable def j3Letters (si : Array ℕ) : Array (Array ℕ) :=
  j3StrongArrs ++ si.map (unpackP 6156 13)

@[expose] noncomputable def j3CheckW (si xe : Array ℕ) (ws : List (List ℕ)) (d : ConjDataP) :
    Bool :=
  let X := xe.map (unpackP 6156 13)
  isInvA 6156 j3UArr (invCand 6156 j3UArr) && si.size == 5 &&
    (allLt 5 fun k =>
      eqA 6156 (compA 6156 (si.map (unpackP 6156 13))[k]! j3StrongArrs[k]!) (idA 6156)) &&
    (allLt (j3Letters si).size fun k => validA 6156 (j3Letters si)[k]!) &&
    xsOK 6156 (j3Letters si) X ws &&
    conjCensusOKW 6156 j3PS (inXL 6156 X) (fun _ => true) (fun _ => false) false false false
      (d.toMain 6156 13) #[] &&
    (d.toMain 6156 13).xs.all (fun a => inXL 6156 X a || inXL 6156 X (compA 6156 j3UArr a)) &&
    (d.toMain 6156 13).xs.length == 8

end CFSG.ComponentClassification.RankTwoSporadic.J3
