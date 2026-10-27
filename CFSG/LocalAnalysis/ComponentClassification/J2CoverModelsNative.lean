module

public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.J2.Certificate
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsData
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsCosets
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsTables

public section

namespace CFSG.ComponentClassification.J2Cover.Models

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native

@[expose] def nth {α : Type} (d : α) : List α → Nat → α
  | [], _ => d
  | a :: _, 0 => a
  | _ :: l, k + 1 => nth d l k

@[expose] def par (x : Nat) : Nat := nth 0 parT x

@[expose] def gen (x : Nat) : Nat := nth 0 genT x

@[expose] def lmul (i b : Nat) : Nat := nth 0 (nth [] lT i) b

@[expose] def pathAux : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, x => if x = 0 then [] else x :: pathAux n (par x)

@[expose] def path (x : Nat) : List Nat := pathAux 128 x

@[expose] def mulIdx (a b : Nat) : Nat := (path a).foldr (fun z acc => lmul (gen z) acc) b

@[expose] def invIdx (x : Nat) : Nat := nth 0 invT x

@[expose] def betaIdx (a : Nat) : Nat := nth 0 betaT a

@[expose, irreducible] def mulTab : Array (Array Nat) :=
  Array.ofFn (n := 128) fun a => Array.ofFn (n := 128) fun d => mulIdx a.val d.val

@[expose, irreducible] def lmulTab : Array (Array Nat) :=
  Array.ofFn (n := 3) fun k => Array.ofFn (n := 128) fun b => lmul k.val b.val

@[expose, irreducible] def betaTab : Array Nat := Array.ofFn (n := 128) fun a => betaIdx a.val

@[expose, irreducible] def invTab : Array Nat := Array.ofFn (n := 128) fun a => invIdx a.val

@[expose] def bitAt (rows : Array Nat) (x y : Nat) : Bool := rows[x]!.testBit y

@[expose] def maskBit (m x : Nat) : Bool := m.testBit x

@[expose] def xorFold (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.fold n (fun i _ acc => acc ^^ p i) false

@[expose] def countFold (n : Nat) (p : Nat → Bool) : Nat :=
  Nat.fold n (fun i _ acc => if p i then acc + 1 else acc) 0

@[expose] def hRowsAll : Array (Array Nat) := #[hRows0, hRows1, hRows2, hRows3, hRows4, hRows5]

@[expose] def hRowsT (j : Nat) : Array Nat := hRowsAll[j]!

@[expose] def bMask (j : Nat) : Nat := nth 0 bMasks j

@[expose] def eBit (j : Nat) : Bool := nth 0 eVec j == 1

@[expose] def qPos (l : Nat) : Nat := nth 0 freePos l

@[expose] def chiMask (k : Nat) : Nat := nth 0 chiMasks k

@[expose] def cobBit (m a d : Nat) : Bool := maskBit m a ^^ maskBit m d ^^ maskBit m mulTab[a]![d]!

@[expose] def fixCountArr (t : Array Nat) : Nat := countFold 315 fun i => t[i]! == i

@[expose, irreducible] def alphaArr : Array Nat :=
  Array.ofFn (n := 315) fun i => ap (CFSG.Sporadic.J2.Native.orbitData ()).alpha i.val

@[expose, irreducible] def betaArr : Array Nat :=
  Array.ofFn (n := 315) fun i => ap (CFSG.Sporadic.J2.Native.orbitData ()).beta i.val

@[expose] def letterArr (k : Nat) : Array Nat := if k = 0 then alphaArr else betaArr

@[expose] def wordArr (w : List Nat) : Array Nat :=
  w.foldr (fun k acc => compA 315 (letterArr k) acc) (idA 315)

@[expose, irreducible] def yArrs : Array (Array Nat) :=
  Array.ofFn (n := 3) fun k => wordArr (nth [] yWords k)

@[expose] def eltArr (x : Nat) : Array Nat :=
  (path x).foldr (fun z acc => compA 315 yArrs[gen z]! acc) (idA 315)

@[expose, irreducible] def eltArrs : Array (Array Nat) :=
  Array.ofFn (n := 128) fun x => eltArr x.val

@[expose] def cosetWordAux : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, i => if i = 0 then [] else cosetWordAux n cosetPar[i]! ++ [cosetLab[i]!]

@[expose] def cosetWord (i : Nat) : List Nat := cosetWordAux 64 i

@[expose, irreducible] def repArrs : Array (Array Nat) :=
  Array.ofFn (n := 4725) fun i => wordArr (cosetWord i.val)

@[expose] def actT (j i : Nat) : Nat := if j = 0 then cosetAct0[i]! else cosetAct1[i]!

@[expose] def witT (j i : Nat) : Nat := if j = 0 then cosetWit0[i]! else cosetWit1[i]!

@[expose, irreducible] def bInvArr : Array Nat := invCand 315 (letterArr 1)

@[expose, irreducible] def bArr : Array Nat := compA 315 (letterArr 1) (compA 315 outerU bInvArr)

@[expose] def yDecomp (k i : Nat) : Nat × Nat :=
  (nth [] yWords k).foldl (fun pc x => (mulTab[pc.1]![witT x pc.2]!, actT x pc.2)) (0, i)

@[expose, irreducible] def decompCols : Array (Array Nat) × Array (Array Nat) := Id.run do
  let Y := (Array.ofFn (n := 3) fun k => Array.ofFn (n := 4725) fun i => yDecomp k.val i.val)
  let mut pc : Array (Array Nat) := #[Array.replicate 4725 0]
  let mut ic : Array (Array Nat) := #[Array.ofFn (n := 4725) fun i => i.val]
  for a in [1:128] do
    let g := gen a
    let q := par a
    let pq := pc[q]!
    let iq := ic[q]!
    let Yg := Y[g]!
    let mut pa : Array Nat := Array.replicate 4725 0
    let mut ia : Array Nat := Array.replicate 4725 0
    for i in [0:4725] do
      let pr := Yg[i]!
      pa := pa.set! i mulTab[pr.1]![pq[pr.2]!]!
      ia := ia.set! i iq[pr.2]!
    pc := pc.push pa
    ic := ic.push ia
  return (pc, ic)

@[expose] def pTab (i a : Nat) : Nat := decompCols.1[a]![i]!

@[expose] def iTab (i a : Nat) : Nat := decompCols.2[a]![i]!

@[expose] def sCheck : Bool :=
  allLt 3 (fun k => allLt 128 fun b =>
    decide (lmul k b < 128) && eqA 315 eltArrs[lmul k b]! (compA 315 yArrs[k]! eltArrs[b]!)) &&
  allLt 128 (fun a => allLt 128 fun b => a == b || !(eqA 315 eltArrs[a]! eltArrs[b]!)) &&
  allLt 128 (fun a => decide (invIdx a < 128) && mulTab[a]![invIdx a]! == 0)

@[expose] def cosetCheck : Bool :=
  allLt 4725 fun i => allLt 2 fun j =>
    decide (actT j i < 4725) && decide (witT j i < 128) &&
      eqA 315 (compA 315 repArrs[i]! (letterArr j))
        (compA 315 eltArrs[witT j i]! repArrs[actT j i]!)

@[expose] def sDecompCheck : Bool :=
  allLt 4725 fun i => allLt 128 fun a =>
    decide (pTab i a < 128) && decide (iTab i a < 4725) &&
      eqA 315 (compA 315 repArrs[i]! eltArrs[a]!) (compA 315 eltArrs[pTab i a]! repArrs[iTab i a]!)

@[expose] def normCocOK (rows : Array Nat) : Bool :=
  allLt 128 (fun x => !(bitAt rows 0 x) && !(bitAt rows x 0)) &&
  allLt 3 (fun k => allLt 128 fun b => allLt 128 fun c =>
    !(bitAt rows (k + 1) b ^^ bitAt rows lmulTab[k]![b]! c ^^ bitAt rows b c ^^
      bitAt rows (k + 1) mulTab[b]![c]!))

@[expose] def treeNormOK (rows : Array Nat) : Bool :=
  allLt 128 fun x => x == 0 || !(bitAt rows (gen x + 1) (par x))

@[expose] def cocycleCheck : Bool :=
  normCocOK fRows &&
  allLt 6 (fun j => normCocOK (hRowsT j) && treeNormOK (hRowsT j) &&
    allLt 6 fun l => decide (qPos l < 384) &&
      bitAt (hRowsT j) (qPos l / 128 + 1) (qPos l % 128) == (j == l)) &&
  allLt 3 (fun k => (allLt 3 fun m => maskBit (chiMask k) (m + 1) == (k == m)) &&
    allLt 128 fun a => allLt 128 fun d =>
      maskBit (chiMask k) mulTab[a]![d]! == (maskBit (chiMask k) a ^^ maskBit (chiMask k) d))

@[expose] def trBit (rows : Array Nat) (a d : Nat) : Bool :=
  let pa := decompCols.1[a]!
  let ia := decompCols.2[a]!
  let pd := decompCols.1[d]!
  xorFold 4725 fun i => bitAt rows pa[i]! pd[ia[i]!]!

@[expose] def transferCheck : Bool :=
  allLt 6 (fun j => !(maskBit (bMask j) 0)) && !(maskBit muMask 0) &&
  allLt 6 (fun j => allLt 3 fun k => allLt 128 fun d =>
    trBit (hRowsT j) (k + 1) d ==
      ((eBit j && bitAt fRows (k + 1) d) ^^ cobBit (bMask j) (k + 1) d)) &&
  allLt 3 (fun k => allLt 128 fun d =>
    (trBit fRows (k + 1) d ^^ cobBit muMask (k + 1) d) == bitAt fRows (k + 1) d)

@[expose] def conjOf (a : Nat) : Nat × List Nat :=
  match conjT.find? (fun e => e.1 == a) with
  | some e => e.2
  | none => (0, [])

@[expose] def involCheck : Bool :=
  fixCountArr eltArrs[4]! == 11 && fixCountArr eltArrs[2]! == 15 &&
  allLt 128 fun a => a == 0 || mulTab[a]![a]! != 0 ||
    (let t := (conjOf a).1
     let g := wordArr (conjOf a).2
     let c := fixCountArr eltArrs[a]!
     ((t == 4 && c == 11 && !(bitAt fRows a a)) || (t == 2 && c == 15 && bitAt fRows a a)) &&
       eqA 315 (compA 315 g eltArrs[a]!) (compA 315 eltArrs[t]! g))

@[expose] def outerCheck : Bool :=
  isInvA 315 outerU outerU && isInvA 315 (letterArr 1) bInvArr &&
  eqA 315 (compA 315 bArr (compA 315 (letterArr 0) bArr)) repArrs[14]! &&
  eqA 315 (compA 315 bArr (compA 315 (letterArr 1) bArr)) repArrs[5]! &&
  allLt 128 (fun a => decide (betaIdx a < 128) &&
    eqA 315 (compA 315 bArr (compA 315 eltArrs[a]! bArr)) eltArrs[betaIdx a]!) &&
  allLt 4725 (fun i => decide (sigmaT[i]! < 4725) && decide (aCoefT[i]! < 128) &&
    eqA 315 (compA 315 bArr (compA 315 repArrs[i]! bArr))
      (compA 315 eltArrs[aCoefT[i]!]! repArrs[sigmaT[i]!]!)) &&
  allLt 4725 (fun i =>
    i == 0 || i == 17 || i == 20 || iTab i 1 != i || iTab i 2 != i || iTab i 3 != i) &&
  [0, 17, 20].all (fun i => allLt 128 fun k => !(eqA 315 bArr (compA 315 eltArrs[k]! repArrs[i]!)))

@[expose] def lamBit (a : Nat) : Bool := maskBit lamMask a

@[expose] def muBit (a : Nat) : Bool := maskBit muMask a

@[expose] def cBit (i a : Nat) : Bool :=
  let s := aCoefT[i]!
  let si := invTab[s]!
  let p := pTab i a
  let bp := betaTab[p]!
  bitAt fRows si s ^^ lamBit p ^^ bitAt fRows si bp ^^
    bitAt fRows mulTab[si]![bp]! aCoefT[iTab i a]!

@[expose] def lambdaCheck : Bool :=
  !(lamBit 0) &&
  allLt 128 (fun a => allLt 128 fun d =>
    (bitAt fRows a d ^^ bitAt fRows betaTab[a]! betaTab[d]!) == cobBit lamMask a d) &&
  allLt 128 (fun a => !(lamBit a ^^ lamBit betaTab[a]!)) &&
  allLt 128 (fun a =>
    (xorFold 4725 (fun i => cBit i a) ^^ muBit a ^^ muBit betaTab[a]!) == lamBit a)

@[expose] def mulR (c c' : Nat) : Nat :=
  mulTab[c % 128]![c' % 128]! +
    128 * ((c / 128 + c' / 128 + (if bitAt fRows (c % 128) (c' % 128) then 1 else 0)) % 2)

@[expose] def tauC (c : Nat) : Nat :=
  betaTab[c % 128]! + 128 * ((c / 128 + (if lamBit (c % 128) then 1 else 0)) % 2)

@[expose] def mulT (eps c c' : Nat) : Nat :=
  let r := mulR (c % 256) (if c / 256 = 1 then tauC (c' % 256) else c' % 256)
  (if eps = 1 ∧ c / 256 = 1 ∧ c' / 256 = 1 then mulR r 128 else r) +
    256 * ((c / 256 + c' / 256) % 2)

@[expose] def centerOK (n : Nat) (mul : Nat → Nat → Nat) : Bool :=
  allLt n fun c =>
    (allLt n fun c' => mul c c' == mul c' c) == (c == 0 || c == 4 || c == 128 || c == 132)

@[expose] def sqCount (n : Nat) (mul : Nat → Nat → Nat) (w : Nat) : Nat :=
  countFold n fun c => mul c c == w

@[expose] def fourthCount (n : Nat) (mul : Nat → Nat → Nat) (w : Nat) : Nat :=
  countFold n fun c => mul (mul c c) (mul c c) == w

@[expose] def rootCounts (n : Nat) (mul : Nat → Nat → Nat) : List (Nat × Nat) :=
  [4, 128, 132].map fun w => (sqCount n mul w, fourthCount n mul w)

@[expose] def groupCheck : Bool :=
  centerOK 256 mulR && rootCounts 256 mulR == [(0, 0), (48, 0), (40, 96)] &&
  centerOK 512 (mulT 0) && rootCounts 512 (mulT 0) == [(0, 0), (48, 64), (56, 160)] &&
  centerOK 512 (mulT 1) && rootCounts 512 (mulT 1) == [(16, 0), (96, 64), (40, 160)]

end CFSG.ComponentClassification.J2Cover.Models
