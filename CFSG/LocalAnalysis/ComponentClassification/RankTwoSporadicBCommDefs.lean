module

public import CFSG.RankThree.Asc83Table.MatCertDefs
public import Certificates.Data.CFSGNative.SectionRank.F2Fast

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.B.Native

open CFSG.SectionRank.Native CFSG.Sporadic.SmallF2.Native CFSG.RankThree.Asc83Table.Native

@[expose] def row (X : Array Nat) (i : Nat) : Nat := X[i]?.getD 0

@[expose] def addRows (d : Nat) (X Y : Array Nat) : Array Nat :=
  Array.ofFn (n := d) fun i => row X i.val ^^^ row Y i.val

@[expose] def zeroRows (d : Nat) : Array Nat := Array.replicate d 0

@[expose] def vecNe (d u w : Nat) : Bool := (u ^^^ w) % 2 ^ d != 0

@[expose] def gen (Ds : Array (Array Nat)) (l : Nat) : Array Nat := Ds[l]?.getD #[]

@[expose] def wordRows (d : Nat) (Ds : Array (Array Nat)) : List Nat → Array Nat
  | [] => idRows d
  | l :: w => w.foldl (fun acc k => frMul d acc (gen Ds k)) (gen Ds l)

@[expose] def polyRows (d : Nat) (Ds : Array (Array Nat)) (ws : List (List Nat)) : Array Nat :=
  ws.foldl (fun acc w => addRows d acc (wordRows d Ds w)) (zeroRows d)

@[expose] def forestGen {α : Type} (d : Nat) (par lab : Array Nat) (z : α) (root : Nat → α)
    (mulD : Nat → α → α) : Array α :=
  (List.range d).foldl (fun acc t =>
    acc.push (if d ≤ par[t]?.getD 0 then root (par[t]?.getD 0 - d)
      else mulD (lab[t]?.getD 0) (acc[par[t]?.getD 0]?.getD z))) #[]

@[expose] def forestRows (d : Nat) (Ds : Array (Array Nat)) (par lab roots : Array Nat) :
    Array Nat :=
  forestGen d par lab 0 (fun i => roots[i]?.getD 0) (fun l v => vecMulN d (gen Ds l) v)

@[expose] def rrefAug (d : Nat) (X : Array Nat) : Array Nat × Array Nat := Id.run do
  let mut A : Array Nat := Array.ofFn (n := d) fun i => row X i.val ||| (1 <<< (d + i.val))
  let mut piv : Array Nat := #[]
  for c in [0:d] do
    let r := piv.size
    let mut p := d
    for i in [r:d] do
      if (A[i]!).testBit c then
        p := i
        break
    if p < d then
      let ap := A[p]!
      A := (A.set! p A[r]!).set! r ap
      for i in [0:d] do
        if i != r && (A[i]!).testBit c then
          A := A.set! i (A[i]! ^^^ ap)
      piv := piv.push c
  return (A, piv)

@[expose] def rref (d cap : Nat) (X : Array Nat) : Array Nat × Array Nat := Id.run do
  let k := X.size
  let mut A := X
  let mut piv : Array Nat := #[]
  for c in [0:d] do
    if piv.size ≤ cap then
      let r := piv.size
      let mut p := k
      for i in [r:k] do
        if (A[i]!).testBit c then
          p := i
          break
      if p < k then
        let ap := A[p]!
        A := (A.set! p A[r]!).set! r ap
        for i in [0:k] do
          if i != r && (A[i]!).testBit c then
            A := A.set! i (A[i]! ^^^ ap)
        piv := piv.push c
  return (A, piv)

@[expose] def echelonOK (d : Nat) (X piv : Array Nat) : Bool :=
  (List.range piv.size).all fun i =>
    decide (piv[i]?.getD 0 < d) && (row X i).testBit (piv[i]?.getD 0) &&
      row X i % 2 ^ (piv[i]?.getD 0) == 0 &&
      (i + 1 == piv.size || decide (piv[i]?.getD 0 < piv[i + 1]?.getD 0))

@[expose] def gather (x : Nat) (piv : Array Nat) : Nat :=
  (List.range piv.size).foldl
    (fun acc j => if x.testBit (piv[j]?.getD 0) then acc ||| (1 <<< j) else acc) 0

@[expose] def mulLow (r : Nat) (Y E : Array Nat) : Array Nat :=
  Y.map fun y => (List.range r).foldl (fun acc j => if y.testBit j then acc ^^^ row E j else acc) 0

@[expose] def rankLe (d m : Nat) (X : Array Nat) : Bool :=
  let (E, piv) := rref d m X
  decide (piv.size ≤ m) && mulLow piv.size (X.map fun x => gather x piv) E == X

structure KerData where
  E : Array Nat
  R : Array Nat
  pivE : Array Nat
  U : Array Nat
  pivU : Array Nat
deriving Inhabited

@[expose] def kerData (d : Nat) (θ : Array Nat) : KerData :=
  let (A, pivE) := rrefAug d θ
  let R := A.map (· >>> d)
  let r := pivE.size
  let (U, pivU) := rref d d ((List.range (d - r)).map fun j => row R (r + j)).toArray
  ⟨A.map (· % 2 ^ d), R, pivE, U, pivU⟩

@[expose] def kerOK (d : Nat) (θ E R pivE U pivU : Array Nat) : Bool :=
  frMul d R θ == E && echelonOK d E pivE && echelonOK d U pivU &&
    (List.range pivU.size).all (fun j => vecMulN d θ (row U j) == 0) &&
    pivE.size + pivU.size == d

structure CommCert where
  mc : MCert
  xreg : Nat
  gens : List Nat
  roots : Array Nat
  thetas : List (List (List Nat))
  par : Array Nat
  lab : Array Nat
  tests : List (Nat × Nat × Nat)
  wrows : List Nat
  bound : Nat
  floor : Nat
  xbound : Nat

@[expose] def candRoots (m i u : Nat) : Array Nat :=
  Array.ofFn (n := m) fun k => if k.val = i then u else 0

@[expose] def candsOf (kers : Array KerData) (m : Nat) : Array (Nat × Nat) :=
  ((List.range m).flatMap fun i =>
    (List.range (kers[i]?.getD default).pivU.size).map fun j => (i, j)).toArray

@[expose] def esOf (d : Nat) (Ds : Array (Array Nat)) (par lab : Array Nat) (m : Nat)
    (Binv : Array Nat) (kers : Array KerData) : Array (Array Nat) :=
  (candsOf kers m).map fun c =>
    frMul d Binv (forestRows d Ds par lab (candRoots m c.1 (row (kers[c.1]?.getD default).U c.2)))

@[expose] def testEntry (d : Nat) (Ds : Array (Array Nat)) (E : Array Nat) (l p q : Nat) : Bool :=
  ((vecMulN d (gen Ds l) (row E p)) ^^^ (vecMulN d E (row (gen Ds l) p))).testBit q

@[expose] def testBits (d : Nat) (Ds : Array (Array Nat)) (tests : List (Nat × Nat × Nat))
    (E : Array Nat) : Nat :=
  ofBits tests.length fun t =>
    testEntry d Ds E (tests[t]?.getD (0, 0, 0)).1 (tests[t]?.getD (0, 0, 0)).2.1
      (tests[t]?.getD (0, 0, 0)).2.2

@[expose] def combRows (d : Nat) (Es : Array (Array Nat)) (mask : Nat) : Array Nat :=
  (List.range Es.size).foldl
    (fun acc c => if mask.testBit c then addRows d acc (Es[c]?.getD #[]) else acc) (zeroRows d)

@[expose] def combBits (as : Array Nat) (mask : Nat) : Nat :=
  (List.range as.size).foldl
    (fun acc c => if mask.testBit c then acc ^^^ (as[c]?.getD 0) else acc) 0

@[expose] def survivorOK (d : Nat) (X : Array Nat) (wrows : List Nat) (bound floor : Nat)
    (N : Array Nat) : Bool :=
  wrows.any (fun t => vecNe d (vecMulN d N (row N t)) (1 <<< t)) ||
    wrows.any (fun t => vecNe d (vecMulN d X (row N t)) (vecMulN d N (row X t))) ||
    N == idRows d || N == X ||
    rankLe d (bound - 1) (addRows d N (idRows d)) ||
    rankLe d (floor - 1) (addRows d (frMul d X N) (idRows d))

@[expose] def commDs (R : Array (Array Nat)) (gens : List Nat) : Array (Array Nat) :=
  (gens.map fun g => R[g]!).toArray

@[expose] def commPart (d : Nat) (R : Array (Array Nat)) (C : CommCert) : Bool :=
  let X := R[C.xreg]!
  let Ds := commDs R C.gens
  let m := C.roots.size
  let Bv := forestRows d Ds C.par C.lab C.roots
  let Binv := (rrefAug d Bv).1.map (· >>> d)
  let thetas := (C.thetas.map (polyRows d Ds)).toArray
  let kers := thetas.map (kerData d)
  let Es := esOf d Ds C.par C.lab m Binv kers
  let As := Es.map (testBits d Ds C.tests)
  decide (thetas.size = m) && C.tests.all (fun t => decide (t.2.1 < d) && decide (t.2.2 < d)) &&
    rankLe d C.xbound (addRows d X (idRows d)) && frMul d Binv Bv == idRows d &&
    (List.range m).all (fun i =>
      vecMulN d (thetas[i]?.getD #[]) (C.roots[i]?.getD 0) == 0 &&
        kerOK d (thetas[i]?.getD #[]) (kers[i]?.getD default).E (kers[i]?.getD default).R
          (kers[i]?.getD default).pivE (kers[i]?.getD default).U (kers[i]?.getD default).pivU) &&
    (List.range (2 ^ Es.size)).all fun mask =>
      combBits As mask != 0 || survivorOK d X C.wrows C.bound C.floor (combRows d Es mask)

@[expose] def commCheck (d : Nat) (sA sB : String) (C : CommCert) : Bool :=
  let O := ops2fr d
  let R := O.regsOf sA sB C.mc.nregs C.mc.prog
  (decide (2 ≤ C.mc.nregs) && C.mc.prog.all (Op.lt C.mc.nregs) &&
    C.mc.facts.all (factOK O R C.mc.nregs)) && commPart d R C

end CFSG.ComponentClassification.RankTwoSporadic.B.Native
