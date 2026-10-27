module

public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import Mathlib.Data.Nat.Notation
public import CFSG.Monster.B.TwoA.Unitary.NData

public section

namespace CFSG.EvenSmallLie.TwoE6.Stroth23Inner

open CFSG.Monster.B.TwoA.Unitary

@[expose] def wordAct (w : List ℕ) (c : ℕ) : ℕ :=
  w.foldl (fun c k => CFSG.Monster.B.Co2.Native.actD 22 n6RowArr[k]! c) c

@[expose] def rowsAct (w : List ℕ) : Array ℕ :=
  Array.ofFn (n := 22) fun t => wordAct w (1 <<< (t : ℕ))

@[expose] def deltaLetter (k : ℕ) : List ℕ := if k = 4 then [2, 1, 1, 4] else [k]

@[expose] def deltaWord (x : List ℕ) : List ℕ := x.flatMap deltaLetter

@[expose] def xorSel (f : ℕ → ℕ) (m : ℕ) : ℕ :=
  (List.range 21).foldl (fun a j => if m.testBit j then a ^^^ f j else a) 0

@[expose] def cycWordsD : Array (List ℕ) :=
  #[[], [0], [6], [7], [8], [9], [16], [4], [0, 0], [0, 6], [0, 7], [0, 8], [0, 16], [0, 4],
    [6, 4], [8, 4], [9, 4], [4, 0], [4, 7], [4, 16], [0, 0, 4]]

@[expose] def gen0D : Array ℕ :=
  #[2, 256, 512, 11, 1024, 2048, 4096, 131072, 1, 2845, 2354, 3345, 4419, 1070019, 149663,
    214588, 231956, 1073920, 428079, 655553, 1183936]

@[expose] def vecD (j : ℕ) : ℕ := wordAct cycWordsD[j]! 155

@[expose] def RD : Array (Array ℕ) := cycWordsD.map fun x => rowsAct (deltaWord x)

@[expose] def SD : Array ℕ :=
  Array.ofFn (n := 22) fun t => xorSel (fun j => (RD[j]!)[(t : ℕ)]!) 3112

@[expose] def cycWordsI : Array (List ℕ) :=
  #[[], [0], [1], [2], [3], [4], [7], [11], [12], [14], [15], [16], [0, 4], [0, 11], [1, 4],
    [2, 3], [4, 3], [0, 4, 3], [1, 4, 3], [2, 3, 4], [2, 3, 4, 16]]

@[expose] def gen0I : Array ℕ :=
  #[2, 3, 3526, 3547, 1623, 5729, 67, 10369, 273, 1090, 2518, 8194, 22232, 10241, 16090, 36290,
    148235, 324357, 110606, 536578, 1052674]

@[expose] def vecI (j : ℕ) : ℕ := wordAct cycWordsI[j]! 714762

@[expose] def RI : Array (Array ℕ) := cycWordsI.map rowsAct

@[expose] def SI : Array ℕ :=
  Array.ofFn (n := 22) fun t => xorSel (fun j => (RI[j]!)[(t : ℕ)]!) 3989

@[expose] def u20MaskI : Array ℕ :=
  #[2445, 33034, 33871, 32843, 33859, 557994, 119154, 174794, 11754, 7960, 2074952, 2076252,
    2096317, 2097064, 2093693, 1607391, 1608729, 1606558, 1616795, 1609631]

end CFSG.EvenSmallLie.TwoE6.Stroth23Inner
