module

public import CFSG.Certificates.CosetTablePresented
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshWord

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.CosetTable
open CFSG.EvenSporadicStandard.Fin76b

@[expose] def lE : List (Fin 8 × Bool) := [(0, true)]
@[expose] def lA : List (Fin 8 × Bool) := [(1, true)]
@[expose] def lB : List (Fin 8 × Bool) := [(2, true)]
@[expose] def lU : List (Fin 8 × Bool) := [(3, true)]
@[expose] def lS : List (Fin 8 × Bool) := [(4, true)]
@[expose] def lR : List (Fin 8 × Bool) := [(5, true)]
@[expose] def lD : List (Fin 8 × Bool) := [(6, true)]
@[expose] def lD' : List (Fin 8 × Bool) := [(7, true)]

@[expose] def wC : List (Fin 8 × Bool) := lA ++ lA ++ lB ++ lB

@[expose] def rel4P : List (List (Fin 8 × Bool)) := [
  [(0,true), (0,true)],
  [(5,true), (5,true)],
  [(3,true), (3,true)],
  [(4,true), (4,true), (4,true)],
  [(3,true), (5,true), (3,true), (5,true)],
  [(2,false), (3,true), (2,false), (3,true)],
  [(4,true), (3,true), (4,false), (3,true)],
  [(2,true), (5,true), (1,false), (5,true)],
  [(1,true), (4,true), (2,false), (4,false)],
  [(1,true), (1,true), (1,true), (1,true)],
  [(2,true), (0,true), (2,false), (0,true)],
  [(3,true), (1,false), (3,true), (1,false)],
  [(4,false), (5,true), (4,false), (5,true)],
  [(1,true), (2,false), (1,false), (2,true)],
  [(1,true), (0,true), (1,false), (0,true)],
  [(4,true), (0,true), (4,false), (0,true)],
  [(1,false), (4,true), (1,false), (4,false), (2,false)],
  [(1,true), (0,true), (3,true), (1,true), (0,true), (3,true)],
  [(3,true), (5,true), (0,true), (3,true), (5,true), (0,true)],
  [(5,true), (4,true), (1,true), (2,true), (5,true), (4,true), (1,true)],
  [(3,true), (1,false), (5,true), (4,true), (1,true), (1,true), (3,true), (2,true), (1,false),
    (5,true), (4,true)],
]

@[expose] def rel4D (α β : ℕ) : List (List (Fin 8 × Bool)) :=
  [ lD ++ lD, lD' ++ lD',
    mkRel (invW lD ++ lE ++ lD) (lE ++ wC),
    mkRel (invW lD ++ lA ++ lD) (lA ++ powW wC α),
    mkRel (invW lD ++ lB ++ lD) (lB ++ powW wC α),
    mkRel (invW lD ++ lU ++ lD) lU,
    mkRel (invW lD' ++ lE ++ lD') (lE ++ lA ++ lA),
    mkRel (invW lD' ++ lA ++ lD') lA,
    mkRel (invW lD' ++ lB ++ lD') (lB ++ powW (lA ++ lA) α),
    mkRel (invW lD' ++ lU ++ lD') lU,
    mkRel (invW lS ++ lD ++ lS) lD',
    mkRel (invW lS ++ lD' ++ lS) (lD ++ lD' ++ powW lU α ++ powW wC β ++ powW lE β),
    mkRel (invW lR ++ lD ++ lR) lD,
    mkRel (invW lR ++ lD' ++ lR) (lD ++ lD' ++ powW lU α ++ powW wC β ++ powW lE β),
    mkRel (invW lD ++ invW lD' ++ lD ++ lD') (powW (lB ++ lB) β),
    mkRel (lD ++ lD' ++ lD ++ lD') (powW (lB ++ lB) β) ]

@[expose] def rel4 (α β : ℕ) : List (List (Fin 8 × Bool)) := rel4P ++ rel4D α β

@[expose] def qGens00 : Array Table :=
  #[#[0,1,2,3,4,15,6,7,8,12,10,11,9,22,23,5,16,17,20,21,18,19,13,14],
  #[2,0,6,3,8,12,1,7,17,5,10,4,15,13,19,9,16,11,18,23,20,14,22,21],
  #[1,6,0,10,4,9,2,3,8,15,16,11,5,20,14,12,7,17,13,19,22,21,18,23],
  #[2,6,0,10,11,12,1,16,17,15,3,4,5,20,21,9,7,8,22,23,13,14,18,19],
  #[4,8,11,0,3,14,17,1,7,19,2,10,21,5,13,23,6,16,9,18,12,20,15,22],
  #[1,0,6,8,7,9,2,4,3,5,17,16,15,19,18,12,11,10,14,13,23,22,21,20],
  #[0,1,2,13,14,5,6,18,19,9,20,21,12,3,4,15,22,23,7,8,10,11,16,17],
  #[5,9,12,3,14,0,15,7,19,1,10,21,2,13,4,6,16,23,18,8,20,11,22,17]]

@[expose] def qGens01 : Array Table :=
  #[#[0,1,2,3,4,16,6,7,8,12,10,11,9,17,15,14,5,13,18,19,23,22,21,20],
  #[2,0,6,3,8,12,1,7,19,5,10,4,16,13,21,22,9,17,18,11,20,15,14,23],
  #[1,6,0,10,4,9,2,3,8,16,18,11,5,23,14,15,12,20,7,19,13,21,22,17],
  #[2,6,0,10,11,12,1,18,19,16,3,4,5,23,22,21,9,20,7,8,17,15,14,13],
  #[4,8,11,0,3,14,19,1,7,21,2,10,22,16,17,13,15,5,6,18,12,23,20,9],
  #[1,0,6,8,7,12,2,4,3,16,19,18,5,21,20,23,9,22,11,10,14,13,17,15],
  #[0,1,2,13,14,16,6,20,21,12,23,22,9,3,4,19,5,18,17,15,7,8,11,10],
  #[5,9,12,3,15,0,16,7,22,1,10,21,2,17,19,4,6,13,18,14,23,11,8,20]]

@[expose] def qGens10 : Array Table :=
  #[#[0,1,2,3,4,5,18,7,8,12,10,11,9,23,14,22,21,17,6,20,19,16,15,13],
  #[2,0,5,3,8,1,12,7,17,6,10,4,18,23,14,16,22,11,9,20,19,15,21,13],
  #[1,5,0,10,4,2,12,3,8,6,14,11,18,20,7,22,21,17,9,13,23,16,15,19],
  #[1,0,5,7,8,2,9,3,4,6,14,17,18,20,10,21,22,11,12,23,13,15,16,19],
  #[4,8,11,0,3,17,15,1,7,21,2,10,16,12,5,19,13,14,22,6,18,23,20,9],
  #[1,0,5,8,7,2,18,4,3,12,17,14,9,21,11,20,23,10,6,22,15,13,19,16],
  #[5,2,1,13,15,0,18,20,21,12,19,16,9,3,23,4,11,22,6,10,7,8,17,14],
  #[6,9,12,14,16,18,0,10,22,1,7,15,2,23,3,11,4,21,5,20,19,17,8,13]]

@[expose] def qGens11 : Array Table :=
  #[#[0,1,2,3,4,5,18,7,8,12,10,11,9,23,14,22,21,17,6,20,19,16,15,13],
  #[2,0,5,3,8,1,12,7,17,6,10,4,18,23,14,16,22,11,9,20,19,15,21,13],
  #[1,5,0,10,4,2,12,3,8,6,14,11,18,20,7,22,21,17,9,13,23,16,15,19],
  #[2,5,0,10,11,1,12,14,17,18,3,4,6,19,7,16,15,8,9,13,23,22,21,20],
  #[4,8,11,0,3,17,15,1,7,21,2,10,16,12,5,19,13,14,22,6,18,23,20,9],
  #[1,0,5,8,7,2,18,4,3,12,17,14,9,21,11,20,23,10,6,22,15,13,19,16],
  #[5,2,1,13,15,0,6,20,21,9,19,16,12,3,23,4,11,22,18,10,7,8,17,14],
  #[6,9,12,14,16,18,0,10,22,1,7,15,2,13,3,11,4,21,5,19,20,17,8,23]]

@[expose] def qGens (α β : ℕ) : Array Table :=
  if α = 0 then (if β = 0 then qGens00 else qGens01) else (if β = 0 then qGens10 else qGens11)

@[expose] def qInvs (α β : ℕ) : Array Table := (qGens α β).map (invT 24)

@[expose] def qCheck (α β : ℕ) : Bool :=
  let g := qGens α β
  enumOK 24 24 g (mulClosureS 24 24 g 4000) 1536 &&
  wordsTrivial 24 (fun i : Fin 8 => g[i.val]!) (fun i : Fin 8 => (qInvs α β)[i.val]!) (rel4 α β) &&
  (List.range 8).all (fun i => invOK 24 g[i]! (qInvs α β)[i]!)

end CFSG.EvenSporadicStandard.M12Std.Yosh
