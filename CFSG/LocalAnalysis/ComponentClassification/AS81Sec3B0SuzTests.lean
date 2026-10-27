module

public import CFSG.Sporadic.SuzOddCore.SylowCheckInputs
public meta import CFSG.Sporadic.SuzOddCore.SylowCheckInputs

public section

namespace CFSG.ComponentClassification.AS81.SuzB0

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.PSL3Four.Native
open CFSG.Sporadic.SuzOddCore

@[expose] def qText : String :=
  include_str "../../../Certificates/Data/CFSGNative/SuzOddCore/suz-b0-q.txt"

@[expose] def qArr (i : Nat) : Array Nat := hexTable 3 1782 (1782 * i) qText

@[expose] def tTab : Array Nat := invRepArr 1

@[expose] def cTab (k : Nat) : Array Nat := (invInnerGenArrs 1)[k]!

@[expose] def tPow (b : Nat) : Array Nat := if b == 1 then tTab else idTab 1782

@[expose] def qProd (v : Nat) : Array Nat :=
  (List.range 6).foldl (fun r i => if v.testBit i then compA 1782 r (qArr i) else r) (idTab 1782)

@[expose] def qMinusBit (v : Nat) : Nat :=
  let b := fun i => if v.testBit i then 1 else 0
  (b 0 * b 1 + b 2 * b 3 + b 4 + b 4 * b 5 + b 5) % 2

@[expose] def qProds : Array (Array Nat) := Array.ofFn (n := 64) fun v => qProd v.val

@[expose] def gammaBit (v w : Nat) : Nat :=
  let a := fun i => if v.testBit i then 1 else 0
  let b := fun i => if w.testBit i then 1 else 0
  (a 1 * b 0 + a 3 * b 2 + a 5 * b 4 + a 4 * b 4 + a 5 * b 5) % 2

@[expose] def qElts : Array (Array Nat) :=
  Array.ofFn (n := 128) fun j => compA 1782 qProds[j.val / 2]! (tPow (j.val % 2))

@[expose] def acts : List (List (Nat × Nat)) :=
  [[(1, 0), (2, 0), (4, 0), (8, 0), (16, 0), (32, 0)],
    [(29, 0), (30, 0), (35, 0), (51, 0), (12, 1), (7, 1)],
    [(45, 0), (46, 0), (51, 1), (19, 1), (11, 0), (12, 1)],
    [(1, 0), (6, 1), (4, 0), (9, 0), (16, 0), (32, 0)],
    [(44, 0), (30, 0), (35, 0), (23, 1), (54, 0), (47, 0)],
    [(45, 1), (46, 1), (39, 1), (43, 1), (31, 0), (32, 0)],
    [(8, 0), (44, 1), (35, 1), (1, 0), (25, 0), (32, 0)],
    [(15, 0), (23, 0), (9, 0), (19, 1), (38, 1), (54, 1)],
    [(29, 0), (30, 0), (51, 0), (35, 1), (12, 1), (11, 0)],
    [(10, 1), (1, 1), (29, 0), (45, 0), (13, 1), (56, 1)]]

@[expose] def act (k i : Nat) : Nat × Nat := (acts.getD k []).getD i (0, 0)

@[expose] def matTab (k : Nat) : Array Nat :=
  Array.ofFn (n := 64) fun v =>
    (List.range 6).foldl (fun r i => if v.val.testBit i then r ^^^ (act k i).1 else r) 0

@[expose] def matTabs : Array (Array Nat) := Array.ofFn (n := 10) fun k => matTab k.val

@[expose] def matEnum : Enum := enumBFS 64 matTabs 25920

@[expose] def noTS3 : Bool :=
  allBelow 64 fun a => allBelow 64 fun b => allBelow 64 fun c =>
    a == 0 || b == 0 || b == a || c == 0 || c == a || c == b || c == (a ^^^ b) ||
      [a, b, c, a ^^^ b, a ^^^ c, b ^^^ c, a ^^^ b ^^^ c].any fun u => qMinusBit u == 1

@[expose] def b0SuzCheck : Bool :=
  permOK 1782 tTab && eqA 1782 (compA 1782 tTab tTab) (idTab 1782) &&
  !(eqA 1782 tTab (idTab 1782)) &&
  (allBelow 6 fun i => permOK 1782 (qArr i) && inM (qArr i) && commutesA (qArr i) tTab) &&
  (allBelow 64 fun v => allBelow 64 fun w =>
    eqA 1782 (compA 1782 qProds[v]! qProds[w]!)
      (compA 1782 qProds[v ^^^ w]! (tPow (gammaBit v w)))) &&
  (allBelow 128 fun j => allBelow 128 fun j' => j == j' || !(eqA 1782 qElts[j]! qElts[j']!)) &&
  (allBelow 10 fun k => permOK 1782 (cTab k) && allBelow 6 fun i =>
    eqA 1782 (compA 1782 (compA 1782 (cTab k) (qArr i)) (invCand 1782 (cTab k)))
      (compA 1782 qProds[(act k i).1]! (tPow (act k i).2))) &&
  enumOK 64 matTabs matEnum && matEnum.tabs.size == 25920 && noTS3

end CFSG.ComponentClassification.AS81.SuzB0
