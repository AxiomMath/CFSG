module

public import Certificates.Data.GMS78RuCzRigidCheck

public section

namespace CFSG.KC.GMS.Gen

open CFSG.ComponentClassification.GMS78.RuCz CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.RankThree.Native
open CFSG.EvenSporadicStandard.Fin76b.AutETable (mt ix tab ev)

section CzJ

variable (relsJ Wq Wv Ww : List (List ℕ)) (sols : List (List (List ℕ))) (normX : List (List ℕ))
  (hCodes : List (List ℕ)) (c2J : List (List ℕ)) (cls : List ℕ)

@[expose] def rigidSearchG (n : ℕ) (M : Array (Array ℕ)) (inv : Array ℕ) (c : ArrCert)
    (gi : List ℕ) : Bool :=
  let rels1 := relsJ.filter fun r => r.all fun l => l < 4
  let rels3 := relsJ.filter fun r => (r.all fun l => l < 8) && !(r.all fun l => l < 4)
  let rels5 := relsJ.filter fun r => !(r.all fun l => l < 8)
  let kq := homTab n M c (Wq.map (evW M inv gi))
  let kw := homTab n M c (Ww.map (evW M inv gi))
  let fix := (List.range n).filter fun a => ix kq a == a
  let d3 := (List.range n).filter fun a =>
    ix kq (ix kq a) == evW M inv [0, 0, a, ix kq a, 0, 0] (Wq.getD 3 [])
  let d5 := (List.range n).filter fun a =>
    ix kq (ix kq a) == evW M inv [0, 0, 0, 0, a, ix kq a] (Wq.getD 5 [])
  let conjT := conjTuples n M inv gi
  let sols := sols.map fun s => s.map (evW M inv gi)
  ix kq (gi.getD 0 0) == gi.getD 0 0 && ix kq (gi.getD 1 0) == gi.getD 1 0 &&
    ix kq (gi.getD 2 0) == gi.getD 3 0 && ix kq (gi.getD 4 0) == gi.getD 5 0 &&
    fix.all fun a0 => fix.all fun a1 =>
      !relsHold M inv rels1 [a0, a1, 0, 0, 0, 0] ||
      d3.all fun a2 =>
        !relsHold M inv rels3 [a0, a1, a2, ix kq a2, 0, 0] ||
        d5.all fun a4 =>
          let t := [a0, a1, a2, ix kq a2, a4, ix kq a4]
          !(relsHold M inv rels5 t && cubeInner n M c gi conjT kw t) || sols.contains t

@[expose] def identSearchG (n : ℕ) (M : Array (Array ℕ)) (inv : Array ℕ) (c : ArrCert)
    (gi : List ℕ) : Bool :=
  let A := (List.range 6).map fun i => evW M inv gi (invCodes ((hCodes.getD i []).drop 3))
  let sols := sols.map fun s => s.map (evW M inv gi)
  let gam := homTab n M c ((List.range 6).map fun i => evW M inv gi (c2J.getD i []))
  let K := #[homTab n M c (Wq.map (evW M inv gi)), homTab n M c (Wv.map (evW M inv gi)),
    homTab n M c (Ww.map (evW M inv gi)), homTab n M c A]
  (List.range 4).all (fun s =>
    let x := evW M inv gi (normX.getD s [])
    (List.range 6).all fun i =>
      mt M (mt M (ix inv x) ((sols.getD s []).getD i 0)) x == A.getD i 0) &&
  relsHold M inv relsJ ((List.range 6).map fun i => evW M inv gi (c2J.getD i [])) &&
  (List.range 4).all (fun s =>
    let s' := cls.getD s 0
    let al := homTab n M c (sols.getD (s + 4) [])
    decide (s' < 4) && (List.range 6).all fun i =>
      ix al (ix gam (gi.getD i 0)) == ix gam ((sols.getD s' []).getD i 0)) &&
  (List.range 4).all (fun j => isInvA n (K.getD j #[]) (invCand n (K.getD j #[]))) &&
  (hCodes.drop 7).all (fun r =>
    let T := r.foldl (fun T l => compA n (letterTab n M inv gi K l) T) (idA n)
    gi.all fun g => ix T g == g) &&
  (List.range n).filter (fun a => gi.all fun g => mt M a g == mt M g a) ==
    [0, evW M inv gi [0, 0]]

end CzJ

end CFSG.KC.GMS.Gen

end
