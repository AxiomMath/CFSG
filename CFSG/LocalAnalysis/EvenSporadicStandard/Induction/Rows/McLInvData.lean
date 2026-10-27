module

public import Certificates.Data.CFSGNative.McL.Certificate
public import Certificates.Data.CFSGNative.PSL3Four.Basic

public section

namespace CFSG.EvenSporadicStandard.McLInv

open CFSG.PSL3Four.Native CFSG.Sporadic.McL.Native CFSG.Sporadic.VecOrbit.Native

@[expose] def wordsT : List (List Int) :=
  [
    [2, -1, 2, -1, -2, -2, -1, -2, -1, -2, -2, -2, 1, 2, 2, 1, 2, 2, 1, -2, 1, -2, 1, 2, 1, -2, -1,
      -2, -2, 1, -2, -2, 1, 2, 2, 1, 2, 1, -2, 1, -2, -2, 1, 2, 2, 2, -1, -2, -2, -1, 2, 2, -1, 2,
      -1, 2, -1, 2, 2, -1, -2, -2, -2, 1, 2, 2, 1, -2, 1, 2, 1, -2, -2, 1, 2, 1],
    [-2, -2, -1, 2, 2, -1, 2, -1, -2, -2, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, -2,
      -1, -2, -2, -1, 2, 2, -1, 2, -1, -2, -2, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1,
      -2, 1, -2, -1, -2, -2, -1, 2, 2, -1, 2, 2, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 1, 2,
      1, -2, 1, -2, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 2],
    [2, 2, 1, -2, 1, 2, 1, -2, -2, 1, 2, 1, 2, 1, 2, 2, 1, -2, 1, 2, 1, -2, 1, -2, -1, -2, -1, -1,
      -2, -1, 2, 2, -1, 2, -1, -2, -1, 2, -1, 2, 2, -1, 2, 1, -2, 1, -2, -2, 1, 2, 2, -1, -2, -1, 2,
      2, -1, 2, -1, 2, -1, 2, 2, -1, 2, 2, -1, -2, -1, 2, 2, -1, -2, -1, 2, 2, -1, -2, -2, -1, 2, 2,
      1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, -2, 1, -2, -2, 1, 2, 2],
    [2, 1, -2, -2, 1, -2, 1, 2, 1, 2, -1, 2, 2, -1, 2, 2, -1, -2, -2, -1, 2, 2, 1, -2, 1, 2, 1, 2,
      1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, -2, -2, -1, -2, -1, -2, -2, -1, 2, 2, 2, 1, 2, 1, -2, 1,
      -2, 1, 2, 1, -2, 1, 2, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, -1, 2, 2, -1,
      2, -1, -2, -2, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, -2],
    [-1, 2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, 1, 2, 2, 1, 2, 1, 2, 2, 1, -2, -2, 1, 2, 1, -2, 1,
      1, 2, 2, 1, -2, -2, 1, 2, 2, 1, -2, -2, 1, 2, 2]
  ]

@[expose] def wordsR : List (List Int) :=
  [
    [-2, -2, 1, 2, 2, 1, 2, 1, -2, 1, -2, 1, 2, 2, 1, -2, -2, -1, 2, -1, 2, 1, -2, 1, -2, -2, 1, 2,
      2, 1, 2, 2, 1, 2, 1, 2, 2, 1, -2, -2, 1, 2, 1, -2, 1, 2, 2, 1, 2, 1, 2, -1, -2, -1, 2, -1, 2,
      -1, -2, -2, -1, -2, -2, -1, 2, -1, -2, -1, 2, -1, 2, 2],
    [-2, -2, 1, 2, 2, 1, -2, 1, -2, -2, 1, 2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -2,
      -1, 2, 2, -1, 2, 2, -1, -2, -1, -2, -2, 1, 2, 2, 1, 2, 1, -2, 1, -2, -2, 1, 2, 1, -2, 1, -2,
      1, 2, 1, -2, -2, 1, 2, 2, 1, -2, 1, 2, 1, 2, 2, 1, 2, 2, 1, -2, -2, 1, 2, 2, 1, -2],
    [-2, -1, 2, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -1, 2, -1, -2, -2, -1, 2, 2,
      2, 2, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1, -2, -2, -2, 1, -2, -2, 1, 2, 2, 1, 2,
      -1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, -2, 1, -2, -2, 1, 2, 2, 1],
    [-2, -2, -1, 2, 2, -1, -2, -1, -2, -1, 2, 2, -1, -2, -1, 2, -1, -2, -2, -1, 2, -1, -2, -1, -2,
      -2, -1, 2, 2, -1, 2, 1, 2, 1, -2, 1, 2, 2, 1, -2, -2, 1, 2, 1, -2, -1, -2, -1, -2, -2, -1, 2,
      2, -1, -2, -1, 2, 2, -1, -2, -2, -1, -2, -2, -1, -2, 1, 2, 2, 1, -2, 1, 2, 2, 1, 2, 2, 1, 2,
      2, -1, -2, -2, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, -2],
    [2, 1, 2, 1, 2, -1, -2, -1, 2, -1, 2, -1, -2, -1, 2, 2, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2,
      -1, -2, -1, 2, 2, -1, 2, -1, -2, -1, -2, -2, -1, 2, 2, 1, 2, 1, -2, -2, 1, -2, -2, -1, -2, -2,
      -1, 2, 2, -1, -2, 1, 2, 2, 1, -2, 1, -2, -2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1,
      2, 2, 1]
  ]

@[expose] def repIdx : List Nat :=
  [2, 3, 4, 5, 8, 13, 14, 15, 18, 19, 24, 30, 33, 47, 56, 57, 60, 61, 62, 66, 67, 83, 105, 108, 135,
    160, 165, 220, 222, 230, 239, 291, 399, 538, 543, 555, 604, 717, 722, 725]

@[expose] def tabOf (T : CFSG.Sporadic.Th.Native.Table) : Tab := T.map UInt32.toNat

@[expose] def wordTab (O : VOrbit) (w : List Int) : Tab :=
  tabOf (CFSG.Sporadic.Th.Native.wordT 275 (genTables O) w)

@[expose] def wordsJ : List (List Int) := [[1], [2]]

@[expose] def gensJ (O : VOrbit) : Array Tab := (wordsJ.map (wordTab O)).toArray

@[expose] def gensT (O : VOrbit) : Array Tab := (wordsT.map (wordTab O)).toArray

@[expose] def gensR (O : VOrbit) : Array Tab := (wordsR.map (wordTab O)).toArray

@[expose] def cover3OK (n : Nat) (T : Array Tab) (O : Array (Array Tab)) : Bool :=
  let idxs := O.map indexOf
  allBelow T.size fun k =>
    T[k]! == idTab n || !(comp n T[k]! (comp n T[k]! T[k]!) == idTab n) ||
      anyBelow O.size fun i => found idxs[i]! O[i]! T[k]!

@[expose] def pairOK (n : Nat) (I : Array Tab) (r : Tab) : Bool :=
  let C := centTabs n I r
  allBelow C.size fun i => allBelow C.size fun j =>
    let p := comp n C[i]! C[j]!
    p == idTab n || !(comp n p (comp n (comp n p p) (comp n p p)) == idTab n)

@[expose] def repsOf (ER : Enum) : Array Tab := (repIdx.map fun k => ER.tabs[k]!).toArray

@[expose] def invCheckWith (gJ gI gT gR gRi : Array Tab) (ET EI ER : Enum) (EO : Array Enum) :
    Bool :=
  enumOK 275 gT ET && ET.tabs.size == 128 && orbitOK 275 gJ gI gJ[0]! EI &&
    coverOK 275 ET.tabs #[EI.tabs] && enumOK 275 gR ER && ER.tabs.size == 729 &&
    repIdx.all (· < ER.tabs.size) && EO.size == (repsOf ER).size &&
    allBelow (repsOf ER).size (fun k => orbitOK 275 gR gRi (repsOf ER)[k]! EO[k]!) &&
    cover3OK 275 ER.tabs (EO.map (·.tabs)) &&
    allBelow (repsOf ER).size (fun k => pairOK 275 EI.tabs (repsOf ER)[k]!)

@[expose] def invCheck (O : VOrbit) : Bool :=
  let gJ := gensJ O
  let gI := gJ.map (invTab 275)
  let gT := gensT O
  let gR := gensR O
  let gRi := gR.map (invTab 275)
  let ER := enumBFS 275 gR 729
  invCheckWith gJ gI gT gR gRi (enumBFS 275 gT 128) (orbitBFS 275 gJ gI gJ[0]! 22275) ER
    ((repsOf ER).map fun r => orbitBFS 275 gR gRi r 27)

@[expose] def mclInvOK : Bool := invCheck (orbitData ())

end CFSG.EvenSporadicStandard.McLInv
