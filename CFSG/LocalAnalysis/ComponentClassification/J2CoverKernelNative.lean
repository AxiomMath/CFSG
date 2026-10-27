
module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelData
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckInputs
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore

public section

namespace CFSG.ComponentClassification.J2Cover.Kernel

open CFSG.Sporadic.Th.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.J2Cover (inP commA arrTable chainTables outerArr twoAArr
  autStrong cent2BStrong cent2BBase cent2AStrong cent2ABase)

@[expose] def genTbls (S : Array (Array Nat)) (k : Nat) : Array Table :=
  ((List.range k).map fun i => arrTable 315 S[i]!).toArray

@[expose] def genInvTbls (S : Array (Array Nat)) (k : Nat) : Array Table :=
  ((List.range k).map fun i => arrTable 315 (invCand 315 S[i]!)).toArray

@[expose] def closedOK (gens gensInv : Array Table) (E : Array Table) : Bool :=
  E.toList.all fun x => (List.range gens.size).all fun l =>
    E.toList.any (fun y => tblEq 315 y (conjT 315 gens[l]! gensInv[l]! x)) &&
      E.toList.any (fun y => tblEq 315 y (conjT 315 gensInv[l]! gens[l]! x))

@[expose] def closureEntries (S : Array (Array Nat)) (k : Nat) (r : Array Nat) : Array Table :=
  (conjClosure 315 (genTbls S k) (genInvTbls S k) (arrTable 315 r) 4000).1

@[expose] def fourTables (S : Array (Array Nat)) (base : Array Nat) : List Table :=
  filterProducts 315 (ordTest 315 4) (chainTables 315 S base) (idT 315) []

@[expose] def classCheck (S : Array (Array Nat)) (k : Nat) (base : Array Nat)
    (reps : List (Array Nat)) (sizes : List Nat) : Bool :=
  repsOK 315 (genTbls S k) (genInvTbls S k) (fourTables S base) (reps.map (arrTable 315)) 4000 &&
    repSizes 315 (genTbls S k) (genInvTbls S k) (reps.map (arrTable 315)) 4000 == sizes &&
    reps.all fun r => isInvA 315 r (invCand 315 r) && ordTest 315 4 (arrTable 315 r) &&
      siftA 315 (rawLevels 315 S base) base 0 r &&
      closedOK (genTbls S k) (genInvTbls S k) (closureEntries S k r)

@[expose] def chainCheck (S : Array (Array Nat)) (base : Array Nat) (W : Array (List Int))
    (sizes : List Nat) (x : Array Nat) : Bool :=
  rawChainOK 315 (S.extract 0 3) S base W 4 && rawOrbitSizes 315 S base == sizes &&
    inP S[0]! && inP S[1]! && inP (compA 315 S[2]! outerArr) &&
    commA S[0]! x && commA S[1]! x && commA S[2]! x

@[expose] def cpACheck : Bool := classCheck cent2BStrong 2 cent2BBase [] []

@[expose] def crACheck : Bool :=
  chainCheck crAStrong crABase crAWords [120, 4] autStrong[0]! &&
    classCheck crAStrong 3 crABase crAReps [60, 20, 60]

@[expose] def cpTCheck : Bool := classCheck cent2AStrong 2 cent2ABase cpTReps [20, 120]

@[expose] def crTCheck : Bool :=
  chainCheck crTStrong crTBase crTWords [160, 8, 3] twoAArr &&
    classCheck crTStrong 3 crTBase crTReps [20, 120, 480, 40]

@[expose] def crUCheck : Bool :=
  chainCheck crUStrong crUBase crUWords [42, 16] outerArr &&
    classCheck crUStrong 3 crUBase crUReps [42, 42]

end CFSG.ComponentClassification.J2Cover.Kernel
