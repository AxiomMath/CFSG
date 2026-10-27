module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeGSCertInputs
public meta import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeGSCertInputs
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.ComponentClassification.GrSLit.HeGS

open CFSG.PSL3Four.Native CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore
open CFSG.Monster.B.Co2.Native CFSG.ComponentClassification.GrSLit.HeldFix

@[expose] def heGS36Pow (t : Tab) : Nat → Tab
  | 0 => idTab 8330
  | k + 1 => comp 8330 t (heGS36Pow t k)

@[expose] def heGS36CTab : Tab :=
  comp 8330 (heGS36Pow (comp 8330 (comp 8330 (comp 8330 (heGen 1) (heGSKTab (heDWords.getD 1 [])))
    (invCand 8330 (heGen 1))) heT1Arr) 8) (heGen 1)

@[expose] def heGS36W1Tab : Tab :=
  comp 8330 (comp 8330 heGS36CTab (heGen 0)) (invCand 8330 heGS36CTab)

@[expose] def heGS36W2Tab : Tab := comp 8330 heGS36W1Tab heT1Arr

@[expose] def heGS36Data : List (List (List Nat)) :=
  [[[8, 2, 1], [1, 2, 8, 8, 8, 8, 8], [1, 8, 3, 8], [8, 8, 8, 8, 8, 3, 8, 8, 8, 8, 8, 1]],
    [[8], [8, 8, 8, 8, 8], [3, 8], [8, 8, 8, 8, 8, 3]],
    [[8, 3, 2], [2, 3, 8, 8, 8, 8, 8], [8, 1, 8, 8],
      [8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 1, 8, 8, 8, 8, 8]],
    [[8, 2, 1], [1, 2, 8, 8, 8, 8, 8], [8, 1, 2], [2, 1, 8, 8, 8, 8, 8]]]

@[expose] def heGS36D (p j : Nat) : List Nat := (heGS36Data.getD p []).getD j []

@[expose] def heGS36Word (p : Nat) : List Nat :=
  heGS36D p 0 ++ hfRep (3 + p / 2) heGSXWord ++ heGS36D p 1 ++ heGS36D p 2 ++
    hfRep (3 + p / 2) heGSXWord ++ heGS36D p 3

@[expose] def heGS36Target (p : Nat) : Tab := if p % 2 = 0 then heGS36W1Tab else heGS36W2Tab

end CFSG.ComponentClassification.GrSLit.HeGS
