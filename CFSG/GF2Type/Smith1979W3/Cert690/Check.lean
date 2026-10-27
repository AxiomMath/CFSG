module

public import CFSG.GF2Type.Smith1979W3.Cert690.Statements

public section

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62

@[expose] def b0n (v w : ℕ) : Bool :=
  (v.testBit 1 && w.testBit 0) ^^ (v.testBit 3 && w.testBit 2) ^^
    (v.testBit 5 && w.testBit 4)

@[expose] def qmulN (x y : ℕ) : ℕ :=
  let a := x % 2
  let v := x / 2
  let b := y % 2
  let w := y / 2
  (a ^^^ b ^^^ (if b0n v w then 1 else 0)) + 2 * (v ^^^ w)

@[expose] def qinvN (x : ℕ) : ℕ :=
  let a := x % 2
  let v := x / 2
  (a ^^^ (if b0n v v then 1 else 0)) + 2 * v

@[expose] def z0N : ℕ := 1

@[expose] def a0N : ℕ := 2

@[expose] def lowIdx (v : ℕ) : ℕ :=
  if v.testBit 0 then 0
  else if v.testBit 1 then 1
  else if v.testBit 2 then 2
  else if v.testBit 3 then 3
  else if v.testBit 4 then 4
  else 5

@[expose] def fTable (g f : ℕ) : Array Bool :=
  (List.range 64).foldl
    (fun (F : Array Bool) v =>
      if v = 0 then F
      else
        let j := lowIdx v
        let e := 1 <<< j
        let w := v ^^^ e
        F.set! v (F[w]! ^^ f.testBit j ^^ b0n (Code.act g w) (Code.act g e) ^^ b0n w e))
    (Array.replicate 64 false)

@[expose] def liftTab (g f : ℕ) : Array ℕ :=
  let F := fTable g f
  Array.ofFn (n := 128) fun x =>
    let v := x.val / 2
    let a := x.val % 2
    (a ^^^ (if F[v]! then 1 else 0)) + 2 * Code.act g v

@[expose] def compTab (s t : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 128) fun x => s[t[x.val]!]!

@[expose] def invTab (t : Array ℕ) : Array ℕ :=
  (List.range 128).foldl
    (fun (r : Array ℕ) x => if t[x]! < 128 then r.set! (t[x]!) x else r)
    (Array.replicate 128 0)

@[expose] def innTab (e : ℕ) : Array ℕ :=
  let ei := qinvN e
  Array.ofFn (n := 128) fun x => qmulN (qmulN ei x.val) e

@[expose] def innTabs (_ : Unit := ()) : Array (Array ℕ) :=
  Array.ofFn (n := 128) fun e => innTab e.val

@[expose] def qmulFlat (_ : Unit := ()) : Array ℕ :=
  Array.ofFn (n := 16384) fun i => qmulN (i.val / 128) (i.val % 128)

@[expose] def hashSetOfArray (A : Array ℕ) : Std.HashSet ℕ :=
  A.foldl (fun s x => s.insert x) (∅ : Std.HashSet ℕ)

@[expose] def isHomTabWith (QT t : Array ℕ) : Bool :=
  let R := Array.range 128
  t.size == 128 &&
  t.all (fun x => decide (x < 128)) &&
  R.all (fun x => R.all (fun y =>
    t[QT[x * 128 + y]!]! == QT[(t[x]!) * 128 + (t[y]!)]!)) &&
  (hashSetOfArray t).size == 128

@[expose] def isHomTab (t : Array ℕ) : Bool :=
  isHomTabWith (qmulFlat ()) t

@[expose] def findInn (IT : Array (Array ℕ)) (t : Array ℕ) : Option ℕ :=
  (List.range IT.size).find? fun e => IT[e]! == t

@[expose] def innRoots (IT : Array (Array ℕ)) (t : Array ℕ) : List ℕ :=
  (List.range IT.size).filter fun e => IT[e]! == t

@[expose] def spanArr (S : List ℕ) : Array ℕ :=
  S.foldl
    (fun (B : Array ℕ) e => if B.contains e then B else B ++ B.map (fun x => x ^^^ e))
    #[0]

@[expose] def enumData (gens : List ℕ) (fuel : ℕ := 1 <<< 17) :
    Array ℕ × Array (ℕ × ℕ) :=
  let gs := gens.toArray
  let rec go (fuel : ℕ) (E : Array ℕ) (par : Array (ℕ × ℕ)) (seen : Std.HashSet ℕ)
      (i : ℕ) : Array ℕ × Array (ℕ × ℕ) :=
    match fuel with
    | 0 => (E, par)
    | f + 1 =>
      if i < E.size then
        let st : Array ℕ × Array (ℕ × ℕ) × Std.HashSet ℕ :=
          (List.range gs.size).foldl
            (fun (st : Array ℕ × Array (ℕ × ℕ) × Std.HashSet ℕ) j =>
              let y := Code.mul (E[i]!) (gs[j]!)
              if st.2.2.contains y then st
              else (st.1.push y, st.2.1.push (i, j), st.2.2.insert y))
            (E, par, seen)
        go f st.1 st.2.1 st.2.2 (i + 1)
      else (E, par)
  go fuel #[Code.one] #[(0, 0)] ((∅ : Std.HashSet ℕ).insert Code.one) 0

@[expose] def enumGroup (gens : List ℕ) (_ : Unit := ()) : Array ℕ :=
  (enumData gens).1

@[expose] def enumParents (gens : List ℕ) (_ : Unit := ()) : Array (ℕ × ℕ) :=
  (enumData gens).2

@[expose] def enumOK (gens : List ℕ) (E : Array ℕ) (par : Array (ℕ × ℕ)) : Bool :=
  let gs := gens.toArray
  let Eset : Std.HashSet ℕ := hashSetOfArray E
  E.size != 0 &&
  E[0]! == Code.one &&
  par.size == E.size &&
  (List.range E.size).all (fun i =>
    i == 0 ||
      (decide (par[i]!.1 < i) && decide (par[i]!.2 < gs.size) &&
        E[i]! == Code.mul (E[par[i]!.1]!) (gs[par[i]!.2]!))) &&
  Eset.size == E.size &&
  (List.range E.size).all (fun i => gs.all fun g => Eset.contains (Code.mul (E[i]!) g)) &&
  gs.all (fun g => E.any fun e => Code.mul g e == Code.one)

@[expose] def codeInv (bound x : ℕ) : ℕ :=
  let rec go (fuel y : ℕ) : ℕ :=
    match fuel with
    | 0 => y
    | f + 1 => if Code.mul y x == Code.one then y else go f (Code.mul y x)
  go bound x

@[expose] def codeOrder (bound x : ℕ) : ℕ :=
  let rec go (fuel y n : ℕ) : ℕ :=
    match fuel with
    | 0 => 0
    | f + 1 => if y == Code.one then n else go f (Code.mul y x) (n + 1)
  go bound x 1

@[expose] def codePow (a n : ℕ) : ℕ :=
  let rec go (fuel acc : ℕ) : ℕ :=
    match fuel with
    | 0 => acc
    | f + 1 => go f (Code.mul acc a)
  go n Code.one

@[expose] def pow2K (a : ℕ) : Bool :=
  codePow a 16 == Code.one

@[expose] def isPow2B (n : ℕ) : Bool :=
  n != 0 && (n &&& (n - 1)) == 0

@[expose] def isoQ (minus : Bool) (g : ℕ) : Bool :=
  (List.range 64).all fun v => qB minus (Code.act g v) == qB minus v

@[expose] def invArr (E : Array ℕ) : Array ℕ :=
  E.map fun x => codeInv E.size x

@[expose] def invMapOf (E invE : Array ℕ) : Std.HashMap ℕ ℕ :=
  (List.range E.size).foldl (fun m i => m.insert (E[i]!) (invE[i]!)) {}

@[expose] def isInvCode (x : ℕ) : Bool :=
  x != Code.one && Code.mul x x == Code.one

@[expose] def invsOf (E : Array ℕ) : Array ℕ :=
  E.filter fun x => isInvCode x

@[expose] def bitCount (n mask : ℕ) : ℕ :=
  (List.range n).foldl (fun k i => if mask.testBit i then k + 1 else k) 0

@[expose] def idxMapOf (A : Array ℕ) : Std.HashMap ℕ ℕ :=
  (List.range A.size).foldl (fun m i => m.insert (A[i]!) i) {}

@[expose] def mulIdxTable (A : Array ℕ) (idx : Std.HashMap ℕ ℕ) : Array (Array ℕ) :=
  Array.ofFn (n := A.size) fun i =>
    Array.ofFn (n := A.size) fun j =>
      idx.getD (Code.mul (A[i.val]!) (A[j.val]!)) A.size

@[expose] def conjIdxTable (A K invK : Array ℕ) (idx : Std.HashMap ℕ ℕ) :
    Array (Array ℕ) :=
  Array.ofFn (n := K.size) fun h =>
    Array.ofFn (n := A.size) fun i =>
      idx.getD (Code.mul (Code.mul (K[h.val]!) (A[i.val]!)) (invK[h.val]!)) A.size

@[expose] def centralMaskTable (A K : Array ℕ) : Array ℕ :=
  Array.ofFn (n := K.size) fun h =>
    (List.range A.size).foldl
      (fun m i =>
        if Code.mul (K[h.val]!) (A[i]!) == Code.mul (A[i]!) (K[h.val]!) then
          m ||| (1 <<< i)
        else m)
      0

@[expose] def maskAllTrue (B : Array Bool) (mask n : ℕ) : Bool :=
  (List.range n).all fun i => !(mask.testBit i) || B[i]!

@[expose] def maskClosed (M : Array (Array ℕ)) (mask n : ℕ) : Bool :=
  (List.range n).all fun i =>
    !(mask.testBit i) ||
      (List.range n).all fun j => !(mask.testBit j) || mask.testBit ((M[i]!)[j]!)

@[expose] def normalizesMask (row : Array ℕ) (mask n : ℕ) : Bool :=
  (List.range n).all fun i => !(mask.testBit i) || mask.testBit (row[i]!)

@[expose] def mapsInto (g : ℕ) (L : List ℕ) : Bool :=
  L.all fun v => L.contains (Code.act g v)

@[expose] def mapsIntoList (g : ℕ) (L M : List ℕ) : Bool :=
  L.all fun v => M.contains (Code.act g v)

@[expose] def sameSet (B : Array ℕ) (L : List ℕ) : Bool :=
  B.size == L.length && L.all (fun x => B.contains x) && B.all (fun x => L.contains x)

@[expose] def distinctTabs (A : Array (Array ℕ)) : Bool :=
  (Array.range A.size).all fun i =>
    (Array.range A.size).all fun j =>
      decide (i ≤ j) || A[i]! != A[j]!

@[expose] def findCommutator (K invK : Array ℕ) (t : ℕ) : Option (ℕ × ℕ) :=
  (List.range K.size).findSome? fun i =>
    (List.range K.size).findSome? fun j =>
      if Code.mul (Code.mul (Code.mul (K[i]!) (K[j]!)) (invK[i]!)) (invK[j]!) == t
      then some (i, j) else none

@[expose] def vPlusVecs : List ℕ := [0, 2, 4, 6, 32, 34, 36, 38]

@[expose] def vStarVecs : List ℕ := [0, 1, 8, 9, 16, 17, 24, 25]

structure PGLData where
  elems : Array ℕ
  par : Array (ℕ × ℕ)
  invs : Array ℕ
  invMap : Std.HashMap ℕ ℕ
  elems0 : Array ℕ
  par0 : Array (ℕ × ℕ)
  invs0 : Array ℕ
  involutions : Array ℕ
  outers : Array ℕ
  commWit : Array (Option (ℕ × ℕ))
  f5Wit : Array (ℕ × ℕ)
  w9 : Array ℕ
  w12 : Array ℕ

@[expose] def pglData (_ : Unit := ()) : PGLData :=
  let dK := enumData kPGLGens
  let K := dK.1
  let invK := invArr K
  let dK0 := enumData kPGL0Gens
  let K0 := dK0.1
  let involutions := invsOf K
  let outers := involutions.filter fun u => !(K0.contains u)
  let commWit := (kPGL0Gens.map fun t => findCommutator K invK t).toArray
  let f5Wit := Array.ofFn (n := 64) fun n =>
    ((List.range vPlusVecs.length).findSome? fun i =>
      (List.range vStarVecs.length).findSome? fun j =>
        if vPlusVecs[i]! ^^^ vStarVecs[j]! == n.val then
          some (vPlusVecs[i]!, vStarVecs[j]!)
        else none).getD (0, 0)
  let orbit9 : Std.HashMap ℕ ℕ :=
    (List.range K.size).foldl
      (fun m i =>
        let y := Code.act (K[i]!) 2
        if m.contains y then m else m.insert y i)
      {}
  let w9 := Array.ofFn (n := 64) fun v =>
    if v.val == 0 then 0 else orbit9.getD v.val K.size
  let u0 := outers[0]!
  let conj12 : Std.HashMap ℕ ℕ :=
    (List.range K.size).foldl
      (fun m i =>
        let h := Code.mul (Code.mul (K[i]!) u0) (invK[i]!)
        if m.contains h then m else m.insert h i)
      {}
  let w12 := outers.map fun u' => conj12.getD u' K.size
  { elems := K, par := dK.2, invs := invK, invMap := invMapOf K invK,
    elems0 := K0, par0 := dK0.2, invs0 := invArr K0,
    involutions := involutions, outers := outers, commWit := commWit, f5Wit := f5Wit,
    w9 := w9, w12 := w12 }

@[expose] def pglF1Of (D : PGLData) : Bool :=
  enumOK kPGLGens D.elems D.par && enumOK kPGL0Gens D.elems0 D.par0 &&
  D.invs.size == D.elems.size &&
  (List.range D.elems.size).all
    (fun i => Code.mul (D.elems[i]!) (D.invs[i]!) == Code.one) &&
  D.invs0.size == D.elems0.size &&
  (List.range D.elems0.size).all
    (fun i => Code.mul (D.elems0[i]!) (D.invs0[i]!) == Code.one)

@[expose] def pglF2Of (_ : PGLData) : Bool :=
  kPGLGens.all fun g => isoQ false g

@[expose] def pglF3Of (D : PGLData) : Bool :=
  D.elems.size == 336 && D.elems0.size == 168

@[expose] def pglF4Of (D : PGLData) : Bool :=
  D.elems0.all (fun x => D.elems.contains x) &&
  (kPGL0Gens.all fun x => kPGLGens.all fun g =>
    Code.mul g (D.invMap.getD g 0) == Code.one &&
    D.elems0.contains (Code.mul (Code.mul g x) (D.invMap.getD g 0))) &&
  (kPGLGens.all fun g => kPGLGens.all fun h =>
    Code.mul g (D.invMap.getD g 0) == Code.one &&
    Code.mul h (D.invMap.getD h 0) == Code.one &&
    D.elems0.contains
      (Code.mul (Code.mul (Code.mul g h) (D.invMap.getD g 0)) (D.invMap.getD h 0))) &&
  D.commWit.size == kPGL0Gens.length &&
  (List.range kPGL0Gens.length).all fun j =>
    match D.commWit[j]! with
    | some (i, x) =>
      decide (i < D.elems.size) && decide (x < D.elems.size) &&
      Code.mul (Code.mul (Code.mul (D.elems[i]!) (D.elems[x]!)) (D.invs[i]!)) (D.invs[x]!) ==
        kPGL0Gens[j]!
    | none => false

@[expose] def pglF5Of (D : PGLData) : Bool :=
  vPlusVecs.all (fun v => qB false v == false) &&
  vStarVecs.all (fun v => qB false v == false) &&
  vPlusVecs.filter (fun v => vStarVecs.contains v) == [0] &&
  D.f5Wit.size == 64 &&
  (List.range 64).all fun n =>
    let p := D.f5Wit[n]!
    vPlusVecs.contains p.1 && vStarVecs.contains p.2 && (p.1 ^^^ p.2) == n

@[expose] def pglF6Of (_ : PGLData) : Bool :=
  kPGL0Gens.all fun g => mapsInto g vPlusVecs && mapsInto g vStarVecs

@[expose] def pglF7Of (D : PGLData) : Bool :=
  D.elems.all fun k =>
    if D.elems0.contains k then true
    else mapsIntoList k vPlusVecs vStarVecs && mapsIntoList k vStarVecs vPlusVecs

@[expose] def pglF8Of (D : PGLData) : Bool :=
  (List.range 64).all fun n =>
    if n == 0 then true
    else
      let B := spanArr ((D.elems0.map fun k => Code.act k n).toList)
      (B.size == 8 && sameSet B vPlusVecs) || (B.size == 8 && sameSet B vStarVecs) ||
        B.size == 64

@[expose] def pglF9Of (D : PGLData) : Bool :=
  let vs := (vPlusVecs ++ vStarVecs).filter fun v => v != 0
  vs.contains 2 && D.w9.size == 64 &&
  vs.all fun e' =>
    let i := D.w9[e']!
    decide (i < D.elems.size) && Code.act (D.elems[i]!) 2 == e'

@[expose] def pglInvolutionsOK (D : PGLData) : Bool :=
  D.elems.all (fun x => isInvCode x == D.involutions.contains x) &&
  D.involutions.all (fun x => D.elems.contains x)

@[expose] def pglOutersOK (D : PGLData) : Bool :=
  D.elems.all (fun x => (isInvCode x && !(D.elems0.contains x)) == D.outers.contains x) &&
  D.outers.all (fun x => D.elems.contains x)

@[expose] def pglF10Of (D : PGLData) : Bool :=
  let es := (List.range 64).filter fun e =>
    e != 0 && !(qB false e) && !(vPlusVecs.contains e) && !(vStarVecs.contains e)
  es.all fun e =>
    let C := D.elems.filter fun k => Code.act k e == e
    let n := C.size
    let idx := idxMapOf C
    let M := mulIdxTable C idx
    let isInv := C.map (fun a => Code.mul a a == Code.one)
    let oneIdx := idx.getD Code.one n
    let conj := conjIdxTable C D.elems D.invs idx
    let cent := centralMaskTable C D.elems
    let badCent := (List.range D.elems.size).foldl
      (fun acc i => if pow2K (D.elems[i]!) then acc else acc.push (cent[i]!)) #[]
    if n == 16 then
      let mexact := (List.range n).all fun i =>
        (List.range n).all fun j =>
          let m := (M[i]!)[j]!
          decide (m < n) && C[m]! == Code.mul (C[i]!) (C[j]!)
      let cexact := (List.range D.elems.size).all fun h =>
        (List.range n).all fun i =>
          let y := (conj[h]!)[i]!
          let z := Code.mul (Code.mul (D.elems[h]!) (C[i]!)) (D.invs[h]!)
          (decide (y < n) && C[y]! == z) || (y == n && !(C.contains z))
      (hashSetOfArray C).size == C.size &&
      decide (oneIdx < n) && C[oneIdx]! == Code.one &&
      mexact && cexact &&
      (List.range (2 ^ n)).all fun mask =>
        if mask.testBit oneIdx && decide (4 ≤ bitCount n mask) &&
            maskAllTrue isInv mask n then
          if maskClosed M mask n then
            let normEq := (List.range D.elems.size).all fun h =>
              normalizesMask (conj[h]!) mask n == (Code.act (D.elems[h]!) e == e)
            let bad2 := badCent.any fun m => (mask &&& m) == mask
            !normEq || bad2
          else true
        else true
    else false

@[expose] def pglF11Of (D : PGLData) : Bool :=
  pglOutersOK D &&
  D.outers.all fun u =>
    let C := D.elems.filter fun k => Code.mul k u == Code.mul u k
    let n := C.size
    let idx := idxMapOf C
    let M := mulIdxTable C idx
    let invC := invArr C
    let conjC := conjIdxTable C C invC idx
    let oneIdx := idx.getD Code.one n
    let uIdx := idx.getD u n
    let pow2 := C.map (fun a => pow2K a)
    if n == 12 then
      let mexact := (List.range n).all fun i =>
        (List.range n).all fun j =>
          let m := (M[i]!)[j]!
          decide (m < n) && C[m]! == Code.mul (C[i]!) (C[j]!)
      let cexact := (List.range n).all fun h =>
        (List.range n).all fun i =>
          let y := (conjC[h]!)[i]!
          let z := Code.mul (Code.mul (C[h]!) (C[i]!)) (invC[h]!)
          (decide (y < n) && C[y]! == z) || (y == n && !(C.contains z))
      let invOK := invC.size == n &&
        (List.range n).all (fun i => Code.mul (C[i]!) (invC[i]!) == Code.one)
      (hashSetOfArray C).size == C.size &&
      decide (oneIdx < n) && C[oneIdx]! == Code.one &&
      decide (uIdx < n) && C[uIdx]! == u &&
      invOK && mexact && cexact &&
      (List.range (2 ^ n)).all fun mask =>
        if mask.testBit oneIdx && maskClosed M mask n && maskAllTrue pow2 mask n &&
            (List.range n).all (fun c => normalizesMask (conjC[c]!) mask n) then
          (List.range n).all fun i => !(mask.testBit i) || i == oneIdx || i == uIdx
        else true
    else false

@[expose] def pglF12Of (D : PGLData) : Bool :=
  pglInvolutionsOK D && pglOutersOK D &&
  D.outers.size != 0 && D.w12.size == D.outers.size &&
  (List.range D.outers.size).all fun j =>
    let i := D.w12[j]!
    decide (i < D.elems.size) &&
    Code.mul (Code.mul (D.elems[i]!) D.outers[0]!) (D.invs[i]!) == D.outers[j]!

@[expose] def pglF13Of (D : PGLData) : Bool :=
  (D.elems0.filter fun w => w != Code.one && Code.mul w w == Code.one).all fun w =>
    (D.elems.filter fun k => Code.mul k w == Code.mul w k).size == 16 &&
    ((List.range 64).filter fun v => Code.act w v == v).length == 16

@[expose] def pglF1 (_ : Unit := ()) : Bool := pglF1Of (pglData ())
@[expose] def pglF2 (_ : Unit := ()) : Bool := pglF2Of (pglData ())
@[expose] def pglF3 (_ : Unit := ()) : Bool := pglF3Of (pglData ())
@[expose] def pglF4 (_ : Unit := ()) : Bool := pglF4Of (pglData ())
@[expose] def pglF5 (_ : Unit := ()) : Bool := pglF5Of (pglData ())
@[expose] def pglF6 (_ : Unit := ()) : Bool := pglF6Of (pglData ())
@[expose] def pglF7 (_ : Unit := ()) : Bool := pglF7Of (pglData ())
@[expose] def pglF8 (_ : Unit := ()) : Bool := pglF8Of (pglData ())
@[expose] def pglF9 (_ : Unit := ()) : Bool := pglF9Of (pglData ())
@[expose] def pglF10 (_ : Unit := ()) : Bool := pglF10Of (pglData ())
@[expose] def pglF11 (_ : Unit := ()) : Bool := pglF11Of (pglData ())
@[expose] def pglF12 (_ : Unit := ()) : Bool := pglF12Of (pglData ())
@[expose] def pglF13 (_ : Unit := ()) : Bool := pglF13Of (pglData ())

@[expose] def pglFactsCheck (_ : Unit := ()) : Bool :=
  let D := pglData ()
  pglF1Of D && pglF2Of D && pglF3Of D && pglF4Of D && pglF5Of D && pglF6Of D &&
    pglF7Of D && pglF8Of D && pglF9Of D && pglF10Of D && pglF11Of D && pglF12Of D &&
    pglF13Of D

structure SqWit where
  g : ℕ
  repIdx : ℕ
  k : ℕ
  psi : Array ℕ
  tp : Array ℕ
  itp : Array ℕ

@[expose] def classMapOfReps (E invE reps : Array ℕ) : Std.HashMap ℕ (ℕ × ℕ) :=
  (List.range reps.size).foldl
    (fun m i =>
      (List.range E.size).foldl
        (fun m j =>
          let h := Code.mul (Code.mul (E[j]!) (reps[i]!)) (invE[j]!)
          if m.contains h then m else m.insert h (i, E[j]!))
        m)
    {}

@[expose] def pglReps : List ℕ := [2166376464, 1108378656]

@[expose] def firstInvIdx (E : Array ℕ) : Option ℕ :=
  (List.range E.size).find? fun i => isInvCode (E[i]!)

@[expose] def twoClassReps (E invE : Array ℕ) : Array ℕ :=
  match firstInvIdx E with
  | none => #[]
  | some i =>
    let r1 := E[i]!
    let m1 := classMapOfReps E invE #[r1]
    match (List.range E.size).find? fun j =>
        isInvCode (E[j]!) && !m1.contains (E[j]!) with
    | none => #[r1]
    | some j => #[r1, E[j]!]

@[expose] def sqWitData (classMap : Std.HashMap ℕ (ℕ × ℕ)) (theta : Array (Array ℕ))
    (invs : Array ℕ) : Array (Option SqWit) :=
  invs.map fun g =>
    match classMap.get? g with
    | some (i, k) =>
      if i < theta.size then
        let psi := liftTab k 0
        let tp := compTab (compTab psi (theta[i]!)) (invTab psi)
        some { g := g, repIdx := i, k := k, psi := psi, tp := tp, itp := invTab tp }
      else none
    | none => none

@[expose] def witMapOf (data : Array (Option SqWit)) : Std.HashMap ℕ SqWit :=
  data.foldl
    (fun m o =>
      match o with
      | some w => m.insert w.g w
      | none => m)
    {}

@[expose] def witOK (E : Array ℕ) (invMap : Std.HashMap ℕ ℕ) (reps : Array ℕ)
    (theta : Array (Array ℕ)) (invs : Array ℕ) (wits : Array (Option SqWit)) : Bool :=
  wits.size == invs.size &&
  (List.range invs.size).all fun j =>
    match wits[j]! with
    | some w =>
      w.g == invs[j]! && E.contains w.k &&
      decide (w.repIdx < reps.size) && decide (w.repIdx < theta.size) &&
      Code.mul w.k (invMap.getD w.k 0) == Code.one &&
      w.psi == liftTab w.k 0 &&
      w.tp == compTab (compTab w.psi (theta[w.repIdx]!)) (invTab w.psi) &&
      w.itp == invTab w.tp &&
      Code.mul (Code.mul w.k (reps[w.repIdx]!)) (invMap.getD w.k 0) == w.g
    | none => false

@[expose] def repThetas (reps : Array ℕ) : Array (Array ℕ) :=
  reps.map fun r => liftTab r 0

@[expose] def repRoot (IT : Array (Array ℕ)) (theta : Array (Array ℕ)) : Array ℕ :=
  theta.map fun t => (innRoots IT (compTab t t)).head?.getD 0

@[expose] def rootsOK (IT : Array (Array ℕ)) (theta : Array (Array ℕ)) : Bool :=
  let root := repRoot IT theta
  (Array.range theta.size).all fun i =>
    let l := innRoots IT (compTab (theta[i]!) (theta[i]!))
    let r := root[i]!
    l.length == 2 && l.contains r && l.filter (fun e => e != r) == [qmulN r z0N]

@[expose] def candVal (IT : Array (Array ℕ)) (theta psi tp itp : Array ℕ) (s : ℕ) : Option ℕ :=
  match findInn IT (compTab theta itp) with
  | some e => if e < 128 then some (qmulN (qmulN (psi[s]!) (tp[e]!)) e) else none
  | none => none

@[expose] def candValOne (IT : Array (Array ℕ)) (theta : Array ℕ) : Option ℕ :=
  match findInn IT theta with
  | some e => if e < 128 then some (qmulN e e) else none
  | none => none

@[expose] def sOf (root : Array ℕ) (b0 b1 : Bool) (i : ℕ) : ℕ :=
  let r := root[i]!
  if (if i == 0 then b0 else b1) then qmulN r z0N else r

@[expose] def certBits : List (Bool × Bool) :=
  [(false, false), (false, true), (true, false), (true, true)]

structure PGLSquareData where
  pgl : PGLData
  reps : Array ℕ
  classMap : Std.HashMap ℕ (ℕ × ℕ)
  theta : Array (Array ℕ)
  root : Array ℕ
  wits : Array (Option SqWit)
  witMap : Std.HashMap ℕ SqWit
  qmulFlat : Array ℕ
  innTabs : Array (Array ℕ)

@[expose] def pglSquareData (_ : Unit := ()) : PGLSquareData :=
  let pgl := pglData ()
  let reps := pglReps.toArray
  let classMap := classMapOfReps pgl.elems pgl.invs reps
  let IT := innTabs ()
  let theta := repThetas reps
  let root := repRoot IT theta
  let wits := sqWitData classMap theta pgl.involutions
  { pgl := pgl, reps := reps, classMap := classMap, theta := theta, root := root,
    wits := wits, witMap := witMapOf wits, qmulFlat := qmulFlat (), innTabs := IT }

@[expose] def pglS1Of (D : PGLSquareData) : Bool :=
  pglInvolutionsOK D.pgl &&
  D.reps.size == 2 &&
  D.reps.all (fun r => D.pgl.elems.contains r && isInvCode r) &&
  D.pgl.elems0.contains (D.reps[0]!) &&
  !(D.pgl.elems0.contains (D.reps[1]!)) &&
  D.pgl.involutions.all (fun g => D.classMap.contains g) &&
  D.classMap.size == D.pgl.involutions.size &&
  D.wits.all (fun o => o.isSome) &&
  witOK D.pgl.elems D.pgl.invMap D.reps D.theta D.pgl.involutions D.wits

@[expose] def pglS2Of (D : PGLSquareData) : Bool :=
  D.theta.all (fun t => isHomTabWith D.qmulFlat t) && rootsOK D.innTabs D.theta

@[expose] def pglS3Of (D : PGLSquareData) : Bool :=
  pglInvolutionsOK D.pgl &&
  witOK D.pgl.elems D.pgl.invMap D.reps D.theta D.pgl.involutions D.wits &&
  D.pgl.involutions.all
      (fun g => (List.range 64).all fun f => isHomTabWith D.qmulFlat (liftTab g f)) &&
  D.wits.all fun o =>
    match o with
    | some w => isHomTabWith D.qmulFlat w.psi
    | none => false

@[expose] def pglS4Of (D : PGLSquareData) : Bool :=
  pglOutersOK D.pgl &&
  rootsOK D.innTabs D.theta &&
  witOK D.pgl.elems D.pgl.invMap D.reps D.theta D.pgl.involutions D.wits &&
  certBits.all fun b =>
    D.pgl.outers.all fun u =>
      match D.witMap.get? u with
      | none => false
      | some w =>
        let sv := (List.range 64).map fun f =>
          candVal D.innTabs (liftTab u f) w.psi w.tp w.itp (sOf D.root b.1 b.2 w.repIdx)
        let vals := sv.filterMap fun o => o
        let existOK := sv.all fun o => o.isSome
        let n0 := (vals.filter fun x => x == 0).length
        let nz := (vals.filter fun x => x == z0N).length
        let sigma1 := (n0 == 8 && nz == 0) || (n0 == 0 && nz == 8)
        let tabs := (List.range 64).map (fun f => liftTab u f) |>.toArray
        let sigma2 := (List.range 64).all fun f =>
          match sv[f]! with
          | none => false
          | some v =>
            if v == 0 || v == z0N then
              let t := tabs[f]!
              let fixed := (List.range 128).filter fun x => t[x]! == x
              fixed.length == 8 &&
              fixed.all (fun x => qmulN x x == 0) &&
              (D.pgl.elems0.filter fun w0 =>
                w0 != Code.one && Code.mul w0 w0 == Code.one &&
                  Code.mul w0 u == Code.mul u w0).all fun w0 =>
                fixed.any fun x => Code.act w0 (x / 2) != x / 2
            else true
        w.g == u && existOK && sigma1 && sigma2 && distinctTabs tabs

@[expose] def pglS1 (_ : Unit := ()) : Bool := pglS1Of (pglSquareData ())
@[expose] def pglS2 (_ : Unit := ()) : Bool := pglS2Of (pglSquareData ())
@[expose] def pglS3 (_ : Unit := ()) : Bool := pglS3Of (pglSquareData ())
@[expose] def pglS4 (_ : Unit := ()) : Bool := pglS4Of (pglSquareData ())

@[expose] def pglSquareCheck (_ : Unit := ()) : Bool :=
  let D := pglSquareData ()
  pglS1Of D && pglS2Of D && pglS3Of D && pglS4Of D

@[expose] def a8Gens : List ℕ :=
  [34647329153, 35704297409, 34630292097, 34630549889, 34629255234]

structure A8Data where
  elems : Array ℕ
  par : Array (ℕ × ℕ)
  inverses : Array ℕ
  invMap : Std.HashMap ℕ ℕ
  reps : Array ℕ
  classMap : Std.HashMap ℕ (ℕ × ℕ)
  involutions : Array ℕ
  theta : Array (Array ℕ)
  root : Array ℕ
  wits : Array (Option SqWit)
  witMap : Std.HashMap ℕ SqWit
  qmulFlat : Array ℕ
  innTabs : Array (Array ℕ)

@[expose] def a8Data (_ : Unit := ()) : A8Data :=
  let d := enumData a8Gens
  let E := d.1
  let invE := invArr E
  let reps := twoClassReps E invE
  let classMap := classMapOfReps E invE reps
  let IT := innTabs ()
  let theta := repThetas reps
  let root := repRoot IT theta
  let involutions := invsOf E
  let wits := sqWitData classMap theta involutions
  { elems := E, par := d.2, inverses := invE, invMap := invMapOf E invE, reps := reps,
    classMap := classMap, involutions := involutions, theta := theta, root := root, wits := wits,
    witMap := witMapOf wits, qmulFlat := qmulFlat (), innTabs := IT }

@[expose] def a8InvolutionsOK (D : A8Data) : Bool :=
  D.elems.all (fun x => isInvCode x == D.involutions.contains x) &&
  D.involutions.all (fun x => D.elems.contains x)

@[expose] def a8S1Of (D : A8Data) : Bool :=
  enumOK a8Gens D.elems D.par &&
  D.inverses.size == D.elems.size &&
  (List.range D.elems.size).all
    (fun i => Code.mul (D.elems[i]!) (D.inverses[i]!) == Code.one) &&
  D.elems.size == 20160 &&
  a8Gens.all (fun g => isoQ false g)

@[expose] def a8S2Of (D : A8Data) : Bool :=
  let r1 := D.reps[0]!
  let r2 := D.reps[1]!
  let m1 := classMapOfReps D.elems D.inverses #[r1]
  let r1First := (firstInvIdx D.elems).map (fun i => D.elems[i]!) == some r1
  let j2 := (List.range D.elems.size).find? fun j =>
    isInvCode (D.elems[j]!) && !m1.contains (D.elems[j]!)
  let r2FirstOutside := j2.map (fun j => D.elems[j]!) == some r2
  a8InvolutionsOK D &&
  D.reps.size == 2 &&
  D.reps.all (fun r => D.elems.contains r && isInvCode r) &&
  r1First && r2FirstOutside &&
  !m1.contains r2 &&
  D.involutions.all (fun g => D.classMap.contains g) &&
  D.classMap.size == D.involutions.size &&
  D.wits.all (fun o => o.isSome) &&
  witOK D.elems D.invMap D.reps D.theta D.involutions D.wits

@[expose] def a8S3Of (D : A8Data) : Bool :=
  D.theta.all (fun t => isHomTabWith D.qmulFlat t) && rootsOK D.innTabs D.theta

@[expose] def a8S4Of (D : A8Data) : Bool :=
  let gens := #[Code.one] ++ D.involutions
  a8InvolutionsOK D &&
  witOK D.elems D.invMap D.reps D.theta D.involutions D.wits &&
  gens.all (fun g => (List.range 64).all fun f => isHomTabWith D.qmulFlat (liftTab g f)) &&
  D.wits.all fun o =>
    match o with
    | some w => isHomTabWith D.qmulFlat w.psi
    | none => false

@[expose] def a8S5Of (D : A8Data) : Bool :=
  let gens := #[Code.one] ++ D.involutions
  a8InvolutionsOK D &&
  rootsOK D.innTabs D.theta &&
  witOK D.elems D.invMap D.reps D.theta D.involutions D.wits &&
  certBits.all fun b =>
    let vals : Array (Option ℕ) :=
      gens.foldl
        (fun (acc : Array (Option ℕ)) g =>
          (List.range 64).foldl
            (fun (acc : Array (Option ℕ)) f =>
              let t := liftTab g f
              if t[a0N]! == a0N then
                acc.push
                  (if g == Code.one then candValOne D.innTabs t
                   else
                     match D.witMap.get? g with
                     | some w =>
                       if w.g == g then
                         candVal D.innTabs t w.psi w.tp w.itp (sOf D.root b.1 b.2 w.repIdx)
                       else none
                     | none => none)
              else acc)
            acc)
        #[]
    let flat := vals.toList.filterMap fun o => o
    let existOK := vals.all fun o => o.isSome
    let na := (flat.filter fun x => x == a0N).length
    let nz := (flat.filter fun x => x == z0N).length
    existOK && vals.size == flat.length && na == 120 &&
      ([72, 336, 408, 672].contains nz)

@[expose] def a8S1 (_ : Unit := ()) : Bool := a8S1Of (a8Data ())
@[expose] def a8S2 (_ : Unit := ()) : Bool := a8S2Of (a8Data ())
@[expose] def a8S3 (_ : Unit := ()) : Bool := a8S3Of (a8Data ())
@[expose] def a8S4 (_ : Unit := ()) : Bool := a8S4Of (a8Data ())
@[expose] def a8S5 (_ : Unit := ()) : Bool := a8S5Of (a8Data ())

@[expose] def a8SquareCheck (_ : Unit := ()) : Bool :=
  let D := a8Data ()
  a8S1Of D && a8S2Of D && a8S3Of D && a8S4Of D && a8S5Of D

end CFSG.GF2Type.Smith1979W3.Cert690

end
