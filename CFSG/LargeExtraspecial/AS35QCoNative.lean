module

public import Std.Data.HashSet.Basic

public section

namespace CFSG.LargeExtraspecial.AS35QCo.Native

@[expose] def ofBitsN (n : Nat) (f : Nat → Bool) : Nat :=
  (List.range n).foldl (fun acc j => if f j then acc ||| (1 <<< j) else acc) 0

@[expose] def ent (c i j : Nat) : Bool := c.testBit (6 * i + j)

@[expose] def dotc (c d i k : Nat) : Bool :=
  (List.range 6).foldl (fun acc j => acc ^^ (ent c i j && ent d j k)) false

@[expose] def mulc (c d : Nat) : Nat := ofBitsN 36 fun p => dotc c d (p / 6) (p % 6)

@[expose] def transc (c : Nat) : Nat := ofBitsN 36 fun p => ent c (p % 6) (p / 6)

@[expose] def idc : Nat := 34630287489

@[expose] def jc : Nat := 4328915976

@[expose] def isSp (c : Nat) : Bool := mulc (mulc (transc c) jc) c == jc

@[expose] def upTab : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 1, 6, 7, 8, 9, 10, 2, 7, 11, 12, 13, 14, 3, 8, 12, 15, 16, 17, 4, 9, 13, 16,
    18, 19, 5, 10, 14, 17, 19, 20]

@[expose] def unTab : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 14, 15, 16, 17, 21, 22, 23, 28, 29, 35]

@[expose] def symc (n : Nat) : Nat := ofBitsN 36 fun p => n.testBit (upTab[p]!)

@[expose] def tauOf (n : Nat) : Nat := idc ^^^ mulc jc (symc n)

@[expose] def allBelowGo (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, i => if f i then allBelowGo f fuel (i + 1) else false

@[expose] def allBelow (f : Nat → Bool) (n : Nat) : Bool := allBelowGo f n 0

@[expose] def pushNew (succ : Nat → List Nat) (st : Array Nat × Std.HashSet Nat) (x : Nat) :
    Array Nat × Std.HashSet Nat :=
  (succ x).foldl (fun st y => if st.2.contains y then st else (st.1.push y, st.2.insert y)) st

@[expose] def bfsGo (succ : Nat → List Nat) (cap : Nat) :
    Nat → Array Nat × Std.HashSet Nat → Nat → Array Nat
  | 0, st, _ => st.1
  | fuel + 1, st, i =>
    if cap ≤ st.1.size then st.1
    else if h : i < st.1.size then bfsGo succ cap fuel (pushNew succ st st.1[i]) (i + 1)
    else st.1

@[expose] def bfs (succ : Nat → List Nat) (cap fuel start : Nat) : Array Nat :=
  bfsGo succ cap fuel (#[start], (∅ : Std.HashSet Nat).insert start) 0

@[expose] def conjSucc (gens : List (Nat × Nat)) (x : Nat) : List Nat :=
  gens.map fun g => mulc (mulc g.1 x) g.2

@[expose] def mulSucc (gens : List Nat) (x : Nat) : List Nat := gens.map fun g => mulc x g

@[expose] def strictInc : List Nat → Bool
  | a :: b :: l => if a < b then strictInc (b :: l) else false
  | _ => true

@[expose] def nodupc (a : Array Nat) : Bool :=
  strictInc (a.toList.mergeSort fun x y => decide (x ≤ y))

@[expose] def spGens : List (Nat × Nat) :=
  [(2410230404, 11669084179), (38672414453, 13722633744)]

@[expose] def repc : Nat → Nat
  | 0 => 4565631105
  | 1 => 1343258784
  | 2 => 1343652000
  | _ => 1108378656

@[expose] def orbitRep (k : Nat) : Array Nat := bfs (conjSucc spGens) 1000000 1000000 (repc k)

@[expose] def allOrbits : Array Nat :=
  orbitRep 0 ++ orbitRep 1 ++ orbitRep 2 ++ orbitRep 3

@[expose] def censusOK : Bool :=
  spGens.all (fun g => isSp g.1 && mulc g.1 g.2 == idc && mulc g.2 g.1 == idc) &&
    (List.range 4).all (fun k => isSp (repc k) && mulc (repc k) (repc k) == idc) &&
    allBelow (fun n => let t := tauOf n
      !(mulc t t == idc) || t == idc || allOrbits.contains t) (2 ^ 21)

@[expose] def witc : Nat × Nat := (2410230404, 11669084179)

@[expose] def bigOrder (x : Nat) : Bool :=
  !(x == idc) && !(mulc x x == idc) && !(mulc (mulc x x) x == idc) &&
    !(mulc (mulc x x) (mulc x x) == idc)

@[expose] def prodOK (k : Nat) : Bool :=
  isSp witc.1 && mulc witc.1 witc.2 == idc && mulc witc.2 witc.1 == idc &&
    bigOrder (mulc (repc k) (mulc (mulc witc.1 (repc k)) witc.2))

@[expose] def centGens : Nat → List (Nat × Nat)
  | 0 => [(34517304523, 34769486923), (63806503299, 52608715175)]
  | _ => [(57767543865, 39766124457), (29301414134, 9106985860)]

@[expose] def centSize : Nat → Nat
  | 0 => 23040
  | _ => 4608

@[expose] def centList (k : Nat) : Array Nat :=
  bfs (mulSucc ((centGens k).map Prod.fst)) 1000000 1000000 idc

@[expose] def smallOrbit (k y : Nat) : Array Nat := bfs (conjSucc (centGens k)) 7 100 y

@[expose] def closedOrbit (k : Nat) (o : Array Nat) : Bool :=
  o.all fun x => (conjSucc (centGens k) x).all fun y => o.contains y

@[expose] def critOrbit (k y : Nat) (o : Array Nat) : Bool :=
  (7 ≤ o.size && nodupc (o.extract 0 7)) || (closedOrbit k o && !o.contains (mulc (repc k) y))

@[expose] def critElt (k y : Nat) : Bool :=
  y == idc || y == repc k || critOrbit k y (smallOrbit k y)

@[expose] def critOK (k : Nat) : Bool :=
  (centGens k).all (fun g => isSp g.1 && mulc g.1 g.2 == idc && mulc g.2 g.1 == idc &&
      mulc g.1 (repc k) == mulc (repc k) g.1) &&
    (orbitRep k).size * centSize k == 1451520 && nodupc (orbitRep k) &&
    (centList k).size == centSize k && nodupc (centList k) &&
    (centList k).all (critElt k)

@[expose] def sp6CheckOK : Bool :=
  censusOK && prodOK 2 && prodOK 3 && critOK 0 && critOK 1

end CFSG.LargeExtraspecial.AS35QCo.Native
