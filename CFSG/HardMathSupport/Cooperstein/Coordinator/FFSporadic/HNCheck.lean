module

public import CFSG.Sporadic.HNSchreier.SeedsCheckInputs

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native

set_option compiler.extract_closed false

@[expose] def hnSlpM (prog : List (List Nat)) : Array (Array (Array Nat)) :=
  prog.foldl (fun R w => R.push (wordM (fun l => R.getD (l - 1) (idM 133)) w)) #[rowsA, rowsB]

@[expose] def hnHeisProg : List (List Nat) := [
    [1, 2], [3, 2], [3, 4], [3, 5], [6, 6], [7, 7], [6, 8], [4, 4], [10, 10], [11, 11], [4, 12],
    [13, 13], [14, 14], [15, 15], [16, 16], [13, 15, 17], [18, 9], [19, 13], [3, 3], [21, 21],
    [22, 22], [23, 23], [22, 24], [25, 1], [26, 21], [27, 20], [28, 20], [29, 29], [30, 30],
    [31, 31], [32, 20], [33, 30], [28, 28], [28, 35], [34, 36], [34, 36], [37, 36], [37, 39],
    [37, 40], [41, 37], [41, 40], [37, 43], [44, 39], [45, 39], [37, 46], [47, 37], [48, 39],
    [49, 39], [42, 50], [37, 37], [52, 52], [1, 2], [54, 2], [54, 55], [54, 56], [57, 54],
    [53, 58], [58, 53], [60, 60], [61, 61], [62, 62], [63, 63], [60, 61, 64], [65, 59], [66, 66],
    [58, 67], [38, 68], [69, 68], [69, 70], [69, 71], [72, 69], [73, 73], [73, 74], [71, 71],
    [76, 76], [77, 77], [71, 77, 78], [75, 79], [80, 80], [81, 81], [82, 82], [80, 81, 83],
    [51, 51], [85, 85], [86, 86], [85, 87], [84, 88], [89, 80], [36, 90], [34, 90], [92, 90],
    [93, 93], [93, 94], [91, 91], [96, 96], [97, 97], [91, 98], [91, 91, 91, 91, 93, 93],
    [100, 100], [101, 101], [102, 95, 95, 95, 95, 95, 102, 93, 93, 93, 93, 93],
    [102, 99, 99, 99, 95, 102, 93, 91, 91, 91], [103, 103, 103, 103, 104, 104, 104, 104, 103, 104],
    [102, 99, 99, 102, 91, 91], [106, 103, 103], [102, 95, 99, 102, 91, 93],
    [108, 103, 103, 103, 103, 104, 104, 104, 104], [109, 109, 109, 109]]

@[expose] def hnHeisX1 : Nat := 103

@[expose] def hnHeisX2 : Nat := 107

@[expose] def hnHeisY1 : Nat := 104

@[expose] def hnHeisY2 : Nat := 110

@[expose] def hnHeisZ : Nat := 105

@[expose] def hnRelOK (R : Array (Array (Array Nat))) (u v : List Nat) : Bool :=
  wordM (fun l => R.getD (l - 1) (idM 133)) u == wordM (fun l => R.getD (l - 1) (idM 133)) v

@[expose] def hnHeisCheck (_ : Unit := ()) : Bool :=
  let R := hnSlpM hnHeisProg
  hnRelOK R [hnHeisX1, hnHeisX1, hnHeisX1, hnHeisX1, hnHeisX1] [] &&
    hnRelOK R [hnHeisX2, hnHeisX2, hnHeisX2, hnHeisX2, hnHeisX2] [] &&
    hnRelOK R [hnHeisY1, hnHeisY1, hnHeisY1, hnHeisY1, hnHeisY1] [] &&
    hnRelOK R [hnHeisY2, hnHeisY2, hnHeisY2, hnHeisY2, hnHeisY2] [] &&
    hnRelOK R [hnHeisZ, hnHeisZ, hnHeisZ, hnHeisZ, hnHeisZ] [] &&
    hnRelOK R [hnHeisX1, hnHeisZ] [hnHeisZ, hnHeisX1] &&
    hnRelOK R [hnHeisX2, hnHeisZ] [hnHeisZ, hnHeisX2] &&
    hnRelOK R [hnHeisY1, hnHeisZ] [hnHeisZ, hnHeisY1] &&
    hnRelOK R [hnHeisY2, hnHeisZ] [hnHeisZ, hnHeisY2] &&
    hnRelOK R [hnHeisX1, hnHeisY1] [hnHeisY1, hnHeisX1, hnHeisZ] &&
    hnRelOK R [hnHeisX2, hnHeisY2] [hnHeisY2, hnHeisX2, hnHeisZ] &&
    hnRelOK R [hnHeisX1, hnHeisX2] [hnHeisX2, hnHeisX1] &&
    hnRelOK R [hnHeisY1, hnHeisY2] [hnHeisY2, hnHeisY1] &&
    hnRelOK R [hnHeisX1, hnHeisY2] [hnHeisY2, hnHeisX1] &&
    hnRelOK R [hnHeisX2, hnHeisY1] [hnHeisY1, hnHeisX2] &&
    notIdM 133 (R.getD (hnHeisZ - 1) (idM 133))

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
