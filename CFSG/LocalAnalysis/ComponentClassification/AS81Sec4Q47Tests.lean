module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Q47Data
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeAutSylowTests
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSylowData

public section

namespace CFSG.ComponentClassification.AS81.Q47

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.ComponentClassification.AS81.HeSylow CFSG.ComponentClassification.GrSLit.HeldFix

@[expose] def addCheck (g : Array ℕ) : Bool :=
  (List.range 64).all fun u => (List.range 64).all fun v => g[u ^^^ v]! == g[u]! ^^^ g[v]!

@[expose] def formCheck (g : Array ℕ) : Bool :=
  (List.range 64).all fun v => q47Form[g[v]!]! == q47Form[v]!

@[expose] def isomCheck (g : Array ℕ) : Bool := validA 64 g && addCheck g && formCheck g

@[expose] def admK (k x : ℕ) : Bool :=
  decide (2 ^ k ≤ x) && q47Form[x]! == q47Form[2 ^ k]! &&
    (List.range k).all fun i => q47Form[2 ^ i ^^^ x]! == q47Form[2 ^ i ^^^ 2 ^ k]!

@[expose] def transCheckO : Bool :=
  q47Trans.length == 6 && (List.range 6).all fun k =>
    q47Trans[k]!.all (fun t => isomCheck t && (List.range k).all fun i => t[2 ^ i]! == 2 ^ i) &&
      (List.range 64).all fun x => !(admK k x) || q47Trans[k]!.any fun t => t[2 ^ k]! == x

@[expose] def bilin (u v : ℕ) : ℕ := (q47Form[u ^^^ v]! + q47Form[u]! + q47Form[v]!) % 2

@[expose] def nondegCheck : Bool :=
  (List.range 64).all fun c => (List.range 64).any fun u =>
    (List.range 6).all fun i => bilin (2 ^ i) u == (c >>> i) % 2

@[expose] def oAll : List (Array ℕ) :=
  q47Trans.foldr (fun T acc => T.flatMap fun t => acc.map fun a => compA 64 t a) [idA 64]

@[expose] def oOrd3 : List (Array ℕ) :=
  oAll.filter fun w => eqA 64 (powN 64 w 3) (idA 64) && !(eqA 64 w (idA 64))

@[expose] def mapsInto (t A B : Array ℕ) : Bool := A.toList.all fun a => B.contains t[a]!

@[expose] def memTab (B : Array ℕ) : Array Bool := Array.ofFn fun v : Fin 64 => B.contains v.val

@[expose] def mapsIntoM (t A : Array ℕ) (m : Array Bool) : Bool := A.toList.all fun a => m[t[a]!]!

@[expose] def l30Tab : Array (Array Bool) := q47L30.toArray.map memTab

@[expose] def sameSet (A B : Array ℕ) : Bool :=
  A.toList.all (B.contains ·) && B.toList.all (A.contains ·)

@[expose] def eightCheck (W : Array ℕ) : Bool :=
  W.size == 8 && W.toList.all (fun a => decide (a < 64)) && decide W.toList.Nodup

@[expose] def tsCheck (W : Array ℕ) : Bool :=
  eightCheck W && W[0]! == 0 &&
    W.toList.all (fun a => W.toList.all fun b => W.contains (a ^^^ b)) &&
    W.toList.all fun a => q47Form[a]! == 0

@[expose] def transCheck (Y : List (Array ℕ)) (W : Array ℕ) : Bool :=
  W.toList.all fun w => w == 0 || Y.any fun y => y[W[1]!]! == w

@[expose] def swapCheck (t : Array ℕ) : Bool :=
  (mapsIntoM t q47W1 (memTab q47W1) && mapsIntoM t q47W2 (memTab q47W2)) ||
    (mapsIntoM t q47W1 (memTab q47W2) && mapsIntoM t q47W2 (memTab q47W1))

@[expose] def evalWord (gs : List (Array ℕ)) (w : List ℕ) : Array ℕ :=
  w.foldr (fun l acc => compA 64 gs[l - 1]! acc) (idA 64)

@[expose] def stabCheck (O : List (Array ℕ)) (W : Array ℕ) (U : List (Array ℕ)) : Bool :=
  let mW := memTab W
  let UL := eltsN 64 U
  enumCheckN 64 U 8 && U.all isomCheck && enumCheckN 64 (U ++ q47YGens) 1344 &&
    (U ++ q47YGens).all (fun t => mapsInto t W W) &&
    (O.filter fun t => mapsIntoM t W mW).length == 1344 &&
    q47YGens.all (fun y => U.all fun u => inLN 64 UL (conjA 64 y u))

@[expose] def witCheck (h : Array ℕ) (ws : List (List ℕ)) : Bool :=
  ws.all (·.all fun l => decide (1 ≤ l) && decide (l ≤ 3)) &&
    enumCheckN 64 (ws.map (evalWord (q47YGens ++ [h]))) 32

@[expose] def witsCheck : Bool :=
  let U₁ := eltsN 64 q47U1Gens
  let U₂ := eltsN 64 q47U2Gens
  (List.range 2).all fun s => (List.range 4).all fun k => (List.range 8).all fun j =>
    let g := (if s == 0 then q47G1 else q47G2)[k]!
    let u := (if s == 0 then U₁ else U₂)[j]!
    witCheck (compA 64 g u) q47Wit[(s * 4 + k) * 8 + j]!

@[expose] def refCheck : Bool :=
  let O := oAll
  let Y := eltsN 64 q47YGens
  enumCheckN 64 q47YGens 168 && q47YGens.all isomCheck &&
    tsCheck q47W1 && tsCheck q47W2 &&
    q47W1.toList.all (fun a => a == 0 || !(q47W2.contains a)) &&
    q47YGens.all (fun y => mapsInto y q47W1 q47W1 && mapsInto y q47W2 q47W2) &&
    transCheck Y q47W1 && transCheck Y q47W2 &&
    q47L30.length == 30 && q47L30.all eightCheck &&
    O.all (fun t => (List.range 30).any (fun j => mapsIntoM t q47W1 l30Tab[j]!) &&
      (List.range 30).any (fun j => mapsIntoM t q47W2 l30Tab[j]!)) &&
    q47OrbRep.length == 4 && q47OrbRep.all eightCheck && q47Orb.length == 30 &&
    (List.range 30).all (fun j =>
      let p := q47Orb[j]!
      (p.1 == 4 && sameSet q47L30[j]! q47W1) || (p.1 == 5 && sameSet q47L30[j]! q47W2) ||
        (decide (p.1 < 4) && decide (p.2 < 168) && mapsInto Y[p.2]! q47OrbRep[p.1]! q47L30[j]!)) &&
    q47G1.length == 4 && q47G2.length == 4 && q47G1.all isomCheck && q47G2.all isomCheck &&
    (List.range 4).all (fun k =>
      mapsInto q47G1[k]! q47W1 q47OrbRep[k]! && mapsInto q47G2[k]! q47W2 q47OrbRep[k]!) &&
    stabCheck O q47W1 q47U1Gens && stabCheck O q47W2 q47U2Gens &&
    q47Wit.length == 64 && witsCheck &&
    enumCheckN 64 q47NGens 336 && q47NGens.all isomCheck &&
    q47YGens.all (inLN 64 (eltsN 64 q47NGens)) && q47NGens.all swapCheck &&
    (O.filter swapCheck).length == 336

@[expose] def key3 (t : Array ℕ) : ℕ := t[1]! + 64 * t[4]! + 4096 * t[16]!

@[expose] def key3Mul (a b : Array ℕ) : ℕ := a[b[1]!]! + 64 * a[b[4]!]! + 4096 * a[b[16]!]!

@[expose] def keyTable (L : Array (Array ℕ)) : Array ℕ :=
  (List.range L.size).foldl (fun a i => a.set! (key3 L[i]!) i) (Array.replicate 262144 0)

@[expose] def matMul (d p : ℕ) (a b : List ℕ) : List ℕ :=
  (List.range (d * d)).map fun e =>
    ((List.range d).map fun k => a[e / d * d + k]! * b[k * d + e % d]!).sum % p

@[expose] def projEq7 (a b : List ℕ) : Bool :=
  (List.range 7).any fun l => l != 0 && a == b.map fun x => x * l % 7

@[expose] def det7 (a : List ℕ) : ℕ := (a[0]! * a[3]! % 7 + 7 - a[1]! * a[2]! % 7) % 7

@[expose] def tableOK (L : Array (Array ℕ)) (Ms : List (List ℕ)) (d p : ℕ) (one : List ℕ)
    (mul : List ℕ → List ℕ → Bool) (scal : List ℕ → Bool) : Bool :=
  let T := keyTable L
  Ms.length == L.size && L[0]! == idA 64 &&
    (List.range L.size).all (fun i => T[key3 L[i]!]! == i) &&
    Ms.all (fun m => m.length == d * d && m.all fun x => decide (x < p)) &&
    Ms[0]! == one &&
    (List.range L.size).all (fun i => (List.range L.size).all fun j =>
      mul (matMul d p Ms[i]! Ms[j]!) Ms[T[key3Mul L[i]! L[j]!]!]!) &&
    (List.range L.size).all fun i => i == 0 || !(scal Ms[i]!)

@[expose] def tableCheck : Bool :=
  tableOK (certN 64 q47YGens).pts q47YMat 3 2 [1, 0, 0, 0, 1, 0, 0, 0, 1] (· == ·)
      (· == [1, 0, 0, 0, 1, 0, 0, 0, 1]) &&
    tableOK (certN 64 q47NGens).pts q47NMat 2 7 [1, 0, 0, 1] projEq7
      (fun m => m[1]! == 0 && m[2]! == 0 && m[0]! == m[3]!) &&
    q47NMat.all fun m => det7 m != 0

@[expose] def repCheck (n : ℕ) (Qg reps : List (Array ℕ)) (z : Array ℕ) : Bool :=
  let Q := eltsN n Qg
  reps.length == 64 && eqA n reps[0]! (idA n) && reps.all (inLN n Q) &&
    (List.range 64).all (fun u => (List.range 64).all fun v =>
      eqA n (mulN n reps[u]! reps[v]!) reps[u ^^^ v]! ||
        eqA n (mulN n reps[u]! reps[v]!) (mulN n reps[u ^^^ v]! z)) &&
    Q.all (fun x => (List.range 64).any fun v => eqA n x reps[v]! || eqA n x (mulN n reps[v]! z)) &&
    (List.range 64).all fun v =>
      (eqA n (mulN n reps[v]! reps[v]!) (idA n) && q47Form[v]! == 0) ||
        (eqA n (mulN n reps[v]! reps[v]!) z && q47Form[v]! == 1)

@[expose] def imgOK (n : ℕ) (reps : List (Array ℕ)) (z g d : Array ℕ) : Bool :=
  validA 64 d && (List.range 64).all fun v =>
    eqA n (conjA n g reps[v]!) reps[d[v]!]! || eqA n (conjA n g reps[v]!) (mulN n reps[d[v]!]! z)

@[expose] def imgsOK (n : ℕ) (reps : List (Array ℕ)) (z : Array ℕ) (gs ds : List (Array ℕ)) :
    Bool :=
  gs.length == ds.length && (List.range gs.length).all fun k => imgOK n reps z gs[k]! ds[k]!

@[expose] def classCheck (D Eb K₁ K₂ : List (Array ℕ)) : Bool :=
  let EL := eltsN 64 Eb
  let L₁ := eltsN 64 K₁
  let L₂ := eltsN 64 K₂
  enumCheckN 64 Eb 4 && enumCheckN 64 K₁ 24 && enumCheckN 64 K₂ 24 &&
    D.all (inLN 64 L₁) && D.all (inLN 64 L₂) &&
    oOrd3.all fun w => !(Eb.all fun e => inLN 64 EL (conjA 64 w e)) ||
      inLN 64 L₁ w || inLN 64 L₂ w || enumCheckN 64 (D ++ [w]) 96

@[expose] def modelCheck (n : ℕ) (Xg Qg Eg Fg : List (Array ℕ)) (z : Array ℕ)
    (reps NE D Eb Fb : List (Array ℕ)) (KE KF : List (List (Array ℕ))) (C : List (Array ℕ)) :
    Bool :=
  let XL := eltsN n Xg
  let EL := eltsN n Eg
  let FL := eltsN n Fg
  repCheck n Qg reps z && enumCheckN n NE 1024 && NE.all (inLN n XL) &&
    NE.all (fun g => Eg.all fun q => inLN n EL (conjA n g q)) &&
    NE.all (fun g => Fg.all fun q => inLN n FL (conjA n g q)) &&
    imgsOK n reps z NE D && imgsOK n reps z Eg Eb && imgsOK n reps z Fg Fb &&
    enumCheckN 64 D 8 && KE.length == 2 && KF.length == 2 &&
    classCheck D Eb KE[0]! KE[1]! && classCheck D Fb KF[0]! KF[1]! &&
    C.length == 4 && C.all isomCheck &&
    (List.range 2).all fun i => (List.range 2).all fun j =>
      let YL := eltsN 64 (KE[i]! ++ KF[j]!)
      enumCheckN 64 (KE[i]! ++ KF[j]!) 168 &&
        q47YGens.all fun y => inLN 64 YL (conjA 64 C[2 * i + j]! y)

@[expose] def q47Check : Bool :=
  transCheckO && nondegCheck && refCheck && tableCheck &&
    modelCheck 16 heSyl16 heSylQ16 heSylE16 heSylF16 heSylZ16 q47Rep16 heSyl16 q47D16 q47Eb16
      q47Fb16 q47KE16 q47KF16 q47C16 &&
    modelCheck 32 hfT0Tabs32.toList heAutQ32 heAutE32 heAutF32 heAutZ32 q47Rep32 q47NE32 q47D32
      q47Eb32 q47Fb32 q47KE32 q47KF32 q47C32

end CFSG.ComponentClassification.AS81.Q47
