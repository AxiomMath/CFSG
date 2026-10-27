module

public import Aesop.BuiltinRules
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.ToDual

public section

namespace CFSG.GH74.GLS.LU.Local.FiveStd

structure E where
  a0 : Fin 5
  a1 : Fin 5
  a2 : Fin 5
  a3 : Fin 5
  b0 : Fin 5
  b1 : Fin 5
  b2 : Fin 5
  b3 : Fin 5
  s : Bool
  deriving DecidableEq, Repr

@[expose] def inv5 (c : Fin 5) : Fin 5 :=
  if c = 1 then 1 else if c = 2 then 3 else if c = 3 then 2 else if c = 4 then 4 else 0

@[expose] def detA (x : E) : Fin 5 := x.a0 * x.a3 - x.a1 * x.a2
@[expose] def detB (x : E) : Fin 5 := x.b0 * x.b3 - x.b1 * x.b2

@[expose] def normE (x : E) : E :=
  let c : Fin 5 := inv5 (if x.a0 ≠ 0 then x.a0 else x.a1)
  ⟨c * x.a0, c * x.a1, c * x.a2, c * x.a3, c * x.b0, c * x.b1, c * x.b2, c * x.b3, x.s⟩

@[expose] def mulE (x y : E) : E :=
  match x.s, y.s with
  | false, false =>
    normE ⟨x.a0 * y.a0 + x.a1 * y.a2, x.a0 * y.a1 + x.a1 * y.a3, x.a2 * y.a0 + x.a3 * y.a2, x.a2 * y.a1 + x.a3 * y.a3,
      x.b0 * y.b0 + x.b1 * y.b2, x.b0 * y.b1 + x.b1 * y.b3, x.b2 * y.b0 + x.b3 * y.b2, x.b2 * y.b1 + x.b3 * y.b3, false⟩
  | false, true =>
    normE ⟨x.a0 * y.a0 + x.a1 * y.a2, x.a0 * y.a1 + x.a1 * y.a3, x.a2 * y.a0 + x.a3 * y.a2, x.a2 * y.a1 + x.a3 * y.a3,
      x.b0 * y.b0 + x.b1 * y.b2, x.b0 * y.b1 + x.b1 * y.b3, x.b2 * y.b0 + x.b3 * y.b2, x.b2 * y.b1 + x.b3 * y.b3, true⟩
  | true, false =>
    normE ⟨x.a0 * y.b0 + x.a1 * y.b2, x.a0 * y.b1 + x.a1 * y.b3, x.a2 * y.b0 + x.a3 * y.b2, x.a2 * y.b1 + x.a3 * y.b3,
      x.b0 * y.a0 + x.b1 * y.a2, x.b0 * y.a1 + x.b1 * y.a3, x.b2 * y.a0 + x.b3 * y.a2, x.b2 * y.a1 + x.b3 * y.a3, true⟩
  | true, true =>
    normE ⟨x.a0 * y.b0 + x.a1 * y.b2, x.a0 * y.b1 + x.a1 * y.b3, x.a2 * y.b0 + x.a3 * y.b2, x.a2 * y.b1 + x.a3 * y.b3,
      x.b0 * y.a0 + x.b1 * y.a2, x.b0 * y.a1 + x.b1 * y.a3, x.b2 * y.a0 + x.b3 * y.a2, x.b2 * y.a1 + x.b3 * y.a3, false⟩

@[expose] def invA (x : E) : Fin 5 × Fin 5 × Fin 5 × Fin 5 :=
  let d := inv5 (detA x)
  (d * x.a3, -(d * x.a1), -(d * x.a2), d * x.a0)

@[expose] def invB (x : E) : Fin 5 × Fin 5 × Fin 5 × Fin 5 :=
  let d := inv5 (detB x)
  (d * x.b3, -(d * x.b1), -(d * x.b2), d * x.b0)

@[expose] def invE (x : E) : E :=
  let ia := invA x
  let ib := invB x
  match x.s with
  | false => normE ⟨ia.1, ia.2.1, ia.2.2.1, ia.2.2.2, ib.1, ib.2.1, ib.2.2.1, ib.2.2.2, false⟩
  | true => normE ⟨ib.1, ib.2.1, ib.2.2.1, ib.2.2.2, ia.1, ia.2.1, ia.2.2.1, ia.2.2.2, true⟩

@[expose] def oneE : E := ⟨1, 0, 0, 1, 1, 0, 0, 1, false⟩

@[expose] def conjE (g x : E) : E := mulE (mulE g x) (invE g)

@[expose] def conjI (g gi x : E) : E := mulE (mulE g x) gi

@[expose] def powE (x : E) : ℕ → E
  | 0 => oneE
  | n + 1 => mulE (powE x n) x

@[expose] def ordAux (x : E) : ℕ → E → ℕ → ℕ
  | 0, _, k => k
  | fuel + 1, y, k => if y = oneE then k else ordAux x fuel (mulE y x) (k + 1)

@[expose] def ordE (x : E) : ℕ := ordAux x 300 x 1

@[expose] def commE (x y : E) : Bool := mulE x y == mulE y x

@[expose] def isNorm (x : E) : Bool := x.a0 = 1 || (x.a0 = 0 && x.a1 = 1)

@[expose] def validE (x : E) : Bool := isNorm x && detA x * detB x == 1

@[expose] def allFin5 : List (Fin 5) := [0, 1, 2, 3, 4]

@[expose] def allBlocks : List (Fin 5 × Fin 5 × Fin 5 × Fin 5) :=
  allFin5.flatMap fun a0 => allFin5.flatMap fun a1 => allFin5.flatMap fun a2 =>
    allFin5.map fun a3 => (a0, a1, a2, a3)

@[expose] def det4 (m : Fin 5 × Fin 5 × Fin 5 × Fin 5) : Fin 5 := m.1 * m.2.2.2 - m.2.1 * m.2.2.1

@[expose] def glBlocks : List (Fin 5 × Fin 5 × Fin 5 × Fin 5) := allBlocks.filter fun m => det4 m ≠ 0
@[expose] def slBlocks : List (Fin 5 × Fin 5 × Fin 5 × Fin 5) := allBlocks.filter fun m => det4 m = 1

@[expose] def Cs : List E :=
  (glBlocks.filter fun a => a.1 = 1 || (a.1 = 0 && a.2.1 = 1)).flatMap fun a =>
    (glBlocks.filter fun b => det4 a * det4 b = 1).flatMap fun b =>
      [⟨a.1, a.2.1, a.2.2.1, a.2.2.2, b.1, b.2.1, b.2.2.1, b.2.2.2, false⟩,
       ⟨a.1, a.2.1, a.2.2.1, a.2.2.2, b.1, b.2.1, b.2.2.1, b.2.2.2, true⟩]

@[expose] def zE : E := ⟨1, 0, 0, 1, 4, 0, 0, 4, false⟩

@[expose] def inL (x : E) (L : List E) : Bool := L.contains x

@[expose] def subL (L M : List E) : Bool := L.all fun x => inL x M

@[expose] def eqL (L M : List E) : Bool := subL L M && subL M L

@[expose] def mulLL (L M : List E) : List E := L.flatMap fun x => M.map fun y => mulE x y

@[expose] def powers (g : E) (n : ℕ) : List E := (List.range n).map fun i => powE g i

@[expose] def ppE (a b : E) (m n : ℕ) : List E := mulLL (powers a m) (powers b n)

@[expose] def prod2 (A B : List E) : List E := mulLL A B
@[expose] def prod3 (A B C : List E) : List E := mulLL (mulLL A B) C

@[expose] def conjLL (c : E) (L : List E) : List E :=
  let ci := invE c
  L.map fun x => conjI c ci x

@[expose] def nodupL (L : List E) : Bool := L.all fun x => (L.filter fun y => y == x).length == 1

@[expose] def dedupL (L : List E) : List E := L.foldl (fun acc x => if inL x acc then acc else acc ++ [x]) []

@[expose] def closureAux (gens : List E) : ℕ → List E → List E
  | 0, L => L
  | fuel + 1, L =>
    let L' := dedupL (L ++ L.flatMap fun x => gens.map fun g => mulE x g)
    if L'.length = L.length then L else closureAux gens fuel L'

@[expose] def closureL (gens : List E) : List E := closureAux gens 64 [oneE]

@[expose] def normG (g : E) (gens L : List E) : Bool :=
  let gi := invE g
  gens.all fun x => inL (conjI g gi x) L

@[expose] def normAll (hs gens L : List E) : Bool := hs.all fun h => normG h gens L

@[expose] def cenG (g : E) (gens : List E) : Bool := gens.all fun x => commE g x

@[expose] def codeE (x : E) : ℕ :=
  ((((((x.a0.val * 5 + x.a1.val) * 5 + x.a2.val) * 5 + x.a3.val) * 5 + x.b0.val) * 5 + x.b1.val) * 5 + x.b2.val) * 5 +
      x.b3.val + 390625 * (if x.s then 1 else 0)

@[expose] def K1l : List E := slBlocks.map fun A => normE ⟨A.1, A.2.1, A.2.2.1, A.2.2.2, 1, 0, 0, 1, false⟩
@[expose] def K2l : List E := slBlocks.map fun B => normE ⟨1, 0, 0, 1, B.1, B.2.1, B.2.2.1, B.2.2.2, false⟩

@[expose] def S0gens : List E :=
  [⟨0, 1, 1, 0, 0, 1, 1, 0, true⟩, ⟨0, 1, 1, 0, 0, 2, 3, 0, true⟩, ⟨0, 1, 1, 0, 1, 0, 0, 4, true⟩, ⟨0, 1, 2, 0, 0, 1, 3, 0, true⟩]

@[expose] def S0 : List E := closureL S0gens

@[expose] def swapsK (t : E) : Bool := K1l.all fun x => inL (conjE t x) K2l

@[expose] def normK1 (u : E) : Bool := K1l.all fun x => inL (conjE u x) K1l

@[expose] def S0s : List E := S0.filter swapsK
@[expose] def S0n : List E := S0.filter normK1

@[expose] def pairCond (t u : E) : Bool :=
  inL t S0s && inL u S0n && ordE t == 2 && ordE u == 2 && u != zE && commE t u

@[expose] def Pairs : List (E × E) :=
  S0.flatMap fun t => (S0.filter fun u => pairCond t u).map fun u => (t, u)

@[expose] def Gam : List E := Cs.filter fun x => !x.s

@[expose] def conjPair (g : E) (p : E × E) : E × E := (conjE g p.1, conjE g p.2)

@[expose] def reps : List (E × E) :=
  [(⟨0, 1, 1, 0, 0, 1, 1, 0, true⟩, ⟨1, 0, 0, 4, 4, 0, 0, 1, false⟩),
   (⟨0, 1, 1, 0, 0, 1, 1, 0, true⟩, ⟨1, 0, 0, 4, 1, 0, 0, 4, false⟩),
   (⟨0, 1, 3, 0, 0, 2, 1, 0, true⟩, ⟨1, 0, 0, 4, 4, 0, 0, 1, false⟩),
   (⟨0, 1, 3, 0, 0, 2, 1, 0, true⟩, ⟨0, 1, 1, 0, 0, 3, 2, 0, false⟩)]

@[expose] def coverCheck : Bool :=
  let orbs := reps.map fun r => Gam.map fun g => conjPair g r
  Pairs.length == 96 && reps.all (fun r => pairCond r.1 r.2) && Pairs.all fun p => orbs.any fun o => o.contains p

@[expose] def inKK (x : E) : Bool := !x.s && detA x == detB x

@[expose] def normK (g : E) : Bool :=
  let gi := invE g
  K1l.all (fun x => inL (conjI g gi x) K1l) && K2l.all fun x => inL (conjI g gi x) K2l

@[expose] def isTorusPair (a b : E) : Bool :=
  ordE a == 4 && ordE b == 4 && commE a b && nodupL (ppE a b 4 4) && normK a && normK b

@[expose] def z4pairs (els4 : List E) : List (E × E) :=
  els4.flatMap fun a => els4.filterMap fun b => if commE a b && nodupL (ppE a b 4 4) then some (a, b) else none

@[expose] def x1 : E := (K1l.filter fun x => ordE x == 5).headD oneE
@[expose] def y1 : E := (K2l.filter fun x => ordE x == 5).headD oneE
@[expose] def R1 : List E := ppE x1 y1 5 5

@[expose] def noInvCheck (H0 : List E) : Bool :=
  (Cs.all fun e => !(ordE e % 2 != 0 && ordE e % 5 != 0) || ordE e == 1 || ordE e == 3) &&
  (Cs.filter fun x => ordE x == 3).all fun r =>
    let cs := H0.map fun h => conjE h r
    cs.any fun x => cs.any fun y => ordE (mulE x y) % 2 == 0 || ordE (mulE x y) % 5 == 0

@[expose] def X1cands : List E :=
  (K1l.filter fun x => ordE x == 5).filter fun g => [2, 3, 4].all fun k => codeE g ≤ codeE (powE g k)

@[expose] def Y1cands : List E :=
  (K2l.filter fun x => ordE x == 5).filter fun g => [2, 3, 4].all fun k => codeE g ≤ codeE (powE g k)

@[expose] def Syl36 : List (E × E × List E) :=
  X1cands.flatMap fun gx => Y1cands.map fun gy => (gx, gy, ppE gx gy 5 5)

@[expose] def sylCover : Bool :=
  nodupL R1 && Syl36.all (fun q => nodupL q.2.2) && Cs.all fun c =>
    let ci := invE c
    let cx := conjI c ci x1
    let cy := conjI c ci y1
    Syl36.any fun q => inL cx q.2.2 && inL cy q.2.2

@[expose] def sylInv (a b : E) : List (E × E × List E) :=
  Syl36.filter fun q => normAll [a, b] [q.1, q.2.1] q.2.2

@[expose] def sylowTorusCheck (Pl : List E) : Bool :=
  let Z4 := z4pairs (Pl.filter fun x => ordE x == 4)
  Syl36.all fun q => Z4.all fun p => !(normAll [p.1, p.2] [q.1, q.2.1] q.2.2) || (normK p.1 && normK p.2)

@[expose] def goodX1 (t u a b : E) (H0 : List E) (g : E) : Bool :=
  let X1 := powers g 5
  let g2 := conjE t g
  let X2 := powers g2 5
  let XX := ppE g g2 5 5
  normAll [a, b] [g] X1 &&
  conjE u g == invE g &&
  commE g g2 && nodupL XX &&
  eqL (Cs.filter fun c => normG c [g2] X2) (prod3 X2 K1l H0) &&
  eqL (Cs.filter fun c => cenG c [g2]) (prod2 X2 K1l) &&
  eqL (Cs.filter fun c => normG c [g, g2] XX) (prod3 XX H0 [oneE, t]) &&
  XX.all (fun h => h == oneE ||
    (let Z := powers h 5
     !(normAll [a, b] [h] Z) || eqL Z X1 || eqL Z X2)) &&
  (XX.filter fun x => commE x t).length == 5

@[expose] def checkX1 (t : E) (Syl : List (E × E × List E)) (good : List E) (w : E) : Bool :=
  let w2 := conjE t w
  let Wsub := ppE w w2 4 4
  commE w w2 && good.any fun g =>
    let XX := ppE g (conjE t g) 5 5
    eqL (closureL [g, w]) K1l &&
    Syl.all fun q => Wsub.any fun v => eqL q.2.2 (conjLL v XX)

@[expose] def PlOf (u : E) : List E := Cs.filter fun x => commE x zE && commE x u

@[expose] def els4Of (u : E) : List E := ((PlOf u).filter fun x => ordE x == 4).filter normK

@[expose] def tpOf (u : E) : List (E × E) :=
  let els := els4Of u
  els.flatMap fun a => els.filterMap fun b => if isTorusPair a b then some (a, b) else none

@[expose] def WlOf (u : E) : List E := K1l.filter fun w => mulE w w == zE && conjE w u == mulE u zE

@[expose] def checkP (t u a b : E) : Bool :=
  let Pl := PlOf u
  let H0 := ppE a b 4 4
  Pl.length == 64 &&
  (tpOf u).all (fun p => inL p.1 H0 && inL p.2 H0) &&
  inL zE H0 && inL u H0 &&
  Pl.all (fun p => normG p [a, b] H0) && Pl.all (fun p => inL (mulE p p) H0) &&
  !(WlOf u).isEmpty &&
  Pl.any (fun p => conjE p t == mulE zE t)

@[expose] def checkW (t u a b : E) : Bool :=
  let H0 := ppE a b 4 4
  let Syl := sylInv a b
  let good := X1cands.filter fun g => goodX1 t u a b H0 g
  (WlOf u).all fun w => checkX1 t Syl good w

@[expose] def checkN (u a b : E) : Bool :=
  noInvCheck (ppE a b 4 4) && sylowTorusCheck (PlOf u)

@[expose] def checkRep (t u : E) : Bool :=
  match (tpOf u).head? with
  | none => false
  | some (a, b) => checkP t u a b && checkW t u a b && checkN u a b

@[expose] def diagCheck : Bool :=
  let Z5reps := (Cs.filter fun x => ordE x == 5).filter fun g => [2, 3, 4].all fun k => codeE g ≤ codeE (powE g k)
  Z5reps.all fun g =>
    let Cent := Cs.filter fun x => commE x g
    let invols := Cent.filter fun τ => ordE τ == 2 && τ != zE
    invols.isEmpty ||
      (let A := Cent.filter fun x => ordE x == 1 || ordE x == 5
       A.length == 25 && A.all inKK && (A.all fun a => A.all fun b => inL (mulE a b) A) &&
       (A.all fun a => Cent.all fun c => inL (conjE c a) A) &&
       (Cs.all fun v => conjE v g != invE g || !normK1 v || A.all fun a => conjE v a == invE a) &&
       invols.all fun τ => eqL Cent (prod2 A [oneE, zE, τ, mulE zE τ]))

@[expose] def baseCheck : Bool :=
  Cs.length == 28800 && Cs.all validE && K1l.all validE && K2l.all validE && S0.all validE &&
  ((Cs.map codeE).mergeSort (· ≤ ·)).Pairwise (· < ·) &&
  nodupL S0 && S0.length == 128 && inL oneE S0 && inL zE S0 && (S0.all fun y => commE zE y) &&
  (S0.all fun x => S0.all fun y => inL (mulE x y) S0) &&
  (S0.all fun x => inL (invE x) S0) &&
  (S0.filter fun x => S0.all fun y => commE x y).length == 2 &&
  (S0.filter inKK).length == 32 &&
  (Cs.all fun c => S0.any fun s => inKK (mulE c (invE s)))

@[expose] def fiveStdCheck : Bool :=
  baseCheck && sylCover && diagCheck && coverCheck && reps.all fun r => checkRep r.1 r.2

end CFSG.GH74.GLS.LU.Local.FiveStd
