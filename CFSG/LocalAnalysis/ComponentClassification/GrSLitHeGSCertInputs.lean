module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixTwoBCheckInputs
public import CFSG.Sporadic.SmallOddCore.HeLocalCheckInputs
public meta import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixTwoBCheckInputs
public meta import CFSG.Sporadic.SmallOddCore.HeLocalCheckInputs
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.ComponentClassification.GrSLit.HeGS

open CFSG.PSL3Four.Native CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore
open CFSG.Monster.B.Co2.Native CFSG.ComponentClassification.GrSLit.HeldFix

abbrev HeGSReg := Tab × Tab

@[expose] def heGSLetter (R : Array HeGSReg) (l : Int) : HeGSReg :=
  if 0 < l then R[l.toNat - 1]! else ((R[(-l).toNat - 1]!).2, (R[(-l).toNat - 1]!).1)

@[expose] def heGSWord (n : Nat) (R : Array HeGSReg) (w : List Int) : HeGSReg :=
  w.foldr (fun l acc => (comp n (heGSLetter R l).1 acc.1, comp n acc.2 (heGSLetter R l).2))
    (idTab n, idTab n)

@[expose] def heGSRun (n : Nat) (R : Array HeGSReg) (prog : List (List Int)) : Array HeGSReg :=
  prog.foldl (fun R w => R.push (heGSWord n R w)) R

@[expose] def heGSOK : Nat → List (List Int) → Bool
  | _, [] => true
  | k, w :: prog => lettersOK k w && heGSOK (k + 1) prog

@[expose] def heGSXWord : List Nat := [8, 3, 2, 1]

@[expose] def heGSFix (t : Tab) : Nat := (List.range 8330).countP fun i => t[i]! == i

@[expose] def heGSC0Tabs : Array Tab := Array.ofFn (n := 9) fun j => heInnerC0 j.val

@[expose] def heGSKTab (w : List Nat) : Tab := wordTabS 8330 heGSC0Tabs w

@[expose] def heGSEW (l : List Nat) : List Nat := (l.map fun j => heDWords.getD j []).flatten

@[expose] def heGSCommW (l l' : List Nat) : List Nat :=
  heGSEW l ++ heGSEW l' ++ (heGSEW l).reverse ++ (heGSEW l').reverse

@[expose] def heGSComm2 (L : List (List Nat)) : List Nat :=
  heGSCommW (L.getD 0 []) (L.getD 1 []) ++ heGSCommW (L.getD 2 []) (L.getD 3 [])

@[expose] def heGST0Comm : List (List Nat) := [[2], [4], [4, 4, 2], [2, 2]]

@[expose] def heGSUComm : List (List Nat) := [[2, 0, 2, 1], [0], [3, 3, 1], [2, 3, 2]]

@[expose] def heGSVWord : List Nat := 0 :: heDWords.getD 1 []

@[expose] def heGSDRep (l : Nat) : Tab := wordTabS 105 heDGens (heDClassWords.getD l [])

@[expose] def heGSVTab : Tab := heGSKTab heGSVWord

@[expose] def heGSGTab : Tab :=
  let z := comp 8330 (comp 8330 (comp 8330 (invCand 8330 (heGen 1)) (heGen 0)) (heGen 1))
    heGSVTab
  comp 8330 (comp 8330 z z) (invCand 8330 (heGen 1))

@[expose] def heGSInit : Array HeGSReg :=
  Array.ofFn (n := 10) fun k =>
    let w := heDWords.getD (k.val % 5) []
    if k.val < 5 then (heGSKTab w, heGSKTab w.reverse) else
      (comp 8330 (comp 8330 heGSGTab (heGSKTab w)) (invCand 8330 heGSGTab),
        comp 8330 (comp 8330 heGSGTab (heGSKTab w.reverse)) (invCand 8330 heGSGTab))

@[expose] def heGSProg : List (List Int) :=
  [[2, 3], [1, 11], [8, 7], [12, 13], [3, 7], [14, 15], [4, -1], [16, 17], [-15, 11], [18, 19],
    [-10, 3], [20, 21], [13, 21], [22, 23], [10, 5], [24, 25], [-19, 25], [26, 27], [17, 6],
    [28, 29], [23, 6], [30, 31], [27, 15], [32, 33], [-29, 33], [34, 35], [10, 29], [36, 37],
    [6, -10], [38, 39], [31, 21], [40, 41], [15, 31], [42, 43], [37, -43], [44, 45], [45, 1],
    [46, 47], [9, -35], [48, 49], [10, 49], [50, 51], [43, -39], [52, 53], [47, 15], [54, 55],
    [19, -35], [56, 57], [47, 41], [58, 59], [-51, 39], [60, 61], [-10, 55], [62, 63], [61, 57],
    [64, 65], [-51, 61], [66, 67], [67, -65], [68, 69], [53, 41], [70, 71], [1, -41], [72, 73],
    [73, 59], [74, 75], [71, -73], [76, 77], [65, -10], [78, 79], [35, -77], [80, 81], [75, 69],
    [82, 83], [83, 75], [84, 85], [51, 79], [86, 87], [75, 79], [88, 89], [-63, 77], [90, 91],
    [41, 87], [92, 93], [63, 81], [94, 95], [81, 91], [96, 97], [-10, 97], [98, 99], [85, 95],
    [100, 101], [-85, 75], [102, 103], [41, 85], [104, 105], [91, 10], [106, 107], [-107, 73],
    [108, 109], [-99, 91], [110, 111], [107, -99], [112, 113], [101, -89], [114, 115],
    [-114, -114, -112, -112, -112, -112, -114, -112, 116], [89, -111], [116, 118],
    [-114, -117, -117, -114, -112, -117, -117, -114, 119], [-103, 93], [119, 121],
    [-112, -114, -117, -114, -120, -117, -112, -117, 122],
    [-120, -120, -117, -120, -120, -117, -120, -120, -120, -120, -120, 123], [-111, 105],
    [122, 125], [-114, -114, -124, -124, -114, -124, 126],
    [-117, -120, -124, -120, -124, -124, -117, -117, -124, 127], [-124, 128], [-121, 118],
    [126, 130], [-114, -117, -120, -112, -112, -120, 131], [-120, -129, -117, -117, -124, 132],
    [117, 124, 133, 117, 120, 133, 129, 129, 129],
    [117, 114, 133, 129, 112, 120, 117, 120, 117, 120, 117, 117, 133, 133, 133, 129]]

end CFSG.ComponentClassification.GrSLit.HeGS
