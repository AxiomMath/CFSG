module

public import CFSG.LargeExtraspecial.S63CD4Check
public import CFSG.Quasithin.Recognition.CertTrialityModel
public import Std.Data.HashSet
public meta import CFSG.LargeExtraspecial.S63CD4Check
public meta import CFSG.Quasithin.Recognition.CertTrialityModel

public section

namespace CFSG.LargeExtraspecial.S63

open CFSG.Quasithin CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native

@[expose] def d4GenMat : List (Matrix (Fin 8) (Fin 8) GF8) :=
  [trialityElt (GF8.ofNat' 1) true, trialityElt (GF8.ofNat' 2) true,
    trialityElt (GF8.ofNat' 4) true, trialityElt (GF8.ofNat' 1) false,
    trialityElt (GF8.ofNat' 2) false, trialityElt (GF8.ofNat' 4) false, trialityMid true,
    trialityMid false]

@[expose] def d4Gens : Array (Array ℕ) := (d4GenMat.map encRows).toArray

@[expose] def wordZ : List ℕ := [6, 0, 6, 0, 6, 0, 6, 0]

@[expose] def wordT : List ℕ := [6, 0, 6, 1, 6, 0, 6, 1]

@[expose] def z0R : Array ℕ := wordR d4Gens wordZ

@[expose] def t0R : Array ℕ := wordR d4Gens wordT

@[expose] def uIdx : List ℕ := [0, 1, 2, 6]

@[expose] def lIdx : List ℕ := [0, 1, 2, 3, 4, 5]

@[expose] def qWords : List (List ℕ) :=
  [[6, 1, 6, 1, 0, 6, 2, 6, 2, 0], [0, 6, 2, 0, 6, 1, 6, 0, 6, 2, 1, 0],
    [2, 6, 0, 6, 1, 6, 2, 0, 6, 0, 6, 1, 0], [6, 2, 1, 6, 2, 6, 0, 6, 1, 0], [2, 1, 6, 2, 1],
    [6, 2, 6, 0, 6, 2, 1, 0, 6, 0, 6, 1, 0], [6, 2, 6, 1, 6, 0, 6, 2, 6, 1, 0],
    [2, 6, 0, 6, 2, 1, 6, 0, 6, 1]]

@[expose] def cWords : List (List ℕ) :=
  [[6, 1, 6, 2, 1, 6, 0, 6, 1, 6, 2, 1, 0], [2, 6, 0, 6, 2, 1, 6, 1, 6, 0],
    [2, 0, 6, 0, 6, 1, 6, 2, 6, 0, 6, 1, 0], [7]]

@[expose] def uGens : Array (Array ℕ) := (uIdx.map fun k => d4Gens[k]!).toArray

@[expose] def lGens : Array (Array ℕ) := (lIdx.map fun k => d4Gens[k]!).toArray

@[expose] def qGens : Array (Array ℕ) := (qWords.map (wordR d4Gens)).toArray

@[expose] def cGens : Array (Array ℕ) := (cWords.map (wordR d4Gens)).toArray

@[expose] def gensOK (gs : Array (Array ℕ)) : Bool :=
  allLt gs.size fun k => mulR gs[k]! gs[k]! == oneR

@[expose] def conjI (g g' x : Array ℕ) : Array ℕ := mulR (mulR g x) g'

structure EnumData where
  El : Array (Array ℕ)
  P : Array ℕ
  K : Array ℕ
  idx : Array ℕ → ℕ
  inv : Array ℕ

structure ClassData where
  T : Array (Array ℕ)
  P : Array ℕ
  K : Array ℕ
  idx : Array ℕ → ℕ

@[expose] def invPow (x : Array ℕ) : Array ℕ := Id.run do
  let mut p := x
  let mut q := oneR
  for _ in [0:64] do
    if p == oneR then return q
    q := p
    p := mulR p x
  return q

@[expose] def mkEnum (gs : Array (Array ℕ)) : EnumData :=
  let e := enumBFS gs
  let m := mkIdx e.1
  { El := e.1, P := e.2.1, K := e.2.2, idx := lookup m,
    inv := e.1.map fun x => lookup m (invPow x) }

@[expose] def mkClass (gs : Array (Array ℕ)) (x : Array ℕ) : ClassData :=
  let e := classBFS gs x
  { T := e.1, P := e.2.1, K := e.2.2, idx := lookup (mkIdx e.1) }

@[expose] def EnumData.ok (D : EnumData) (gs : Array (Array ℕ)) (n : ℕ) : Bool :=
  enumOK gs D.El D.P D.K D.idx && D.El.size == n

@[expose] def EnumData.invOK (D : EnumData) (n : ℕ) : Bool :=
  allLt n fun i => decide (D.inv[i]! < n) && mulR D.El[i]! D.El[D.inv[i]!]! == oneR

@[expose] def ClassData.ok (D : ClassData) (gs : Array (Array ℕ)) (x : Array ℕ) (n : ℕ) : Bool :=
  classTreeOK gs x D.T D.P D.K D.idx && D.T.size == n

@[expose] def d4ClassCheckOn (cz ct : ClassData) (eu : EnumData) : Bool :=
  gensOK d4Gens && cz.ok d4Gens z0R 819 && ct.ok d4Gens t0R 68796 && gensOK uGens &&
  eu.ok uGens 4096 &&
  allLt 4096 fun i => !(mulR eu.El[i]! eu.El[i]! == oneR) || eu.El[i]! == oneR ||
    memR cz.T cz.idx eu.El[i]! || memR ct.T ct.idx eu.El[i]!

@[expose] def d4ClassCheck : Bool :=
  d4ClassCheckOn (mkClass d4Gens z0R) (mkClass d4Gens t0R) (mkEnum uGens)

@[expose] def twoSet (D : EnumData) (c3 : ℕ) : List ℕ :=
  (List.range 3072).filter fun i => sq12R D.El[i]! == oneR &&
    sq12R (mulR D.El[i]! (conjI D.El[c3]! D.El[D.inv[c3]!]! D.El[i]!)) == oneR

@[expose] def zSet (D : EnumData) (P2 : List ℕ) : List ℕ :=
  P2.filter fun i => P2.all fun j => mulR D.El[i]! D.El[j]! == mulR D.El[j]! D.El[i]!

@[expose] def commI (x x' c c' : Array ℕ) : Array ℕ := mulR (mulR x' c') (mulR x c)

@[expose] def d4BCheckOn (D : EnumData) (c3 : ℕ) (P2 Z : List ℕ) : Bool :=
  gensOK cGens && (allLt cGens.size fun k => mulR cGens[k]! t0R == mulR t0R cGens[k]!) &&
  D.ok cGens 3072 && D.invOK 3072 && decide (c3 < 3072) && decide (Z.length ≤ 8) &&
  P2.all fun i => Z.contains i || (List.range 3072).any fun c =>
    let w := commI D.El[i]! D.El[D.inv[i]!]! D.El[c]! D.El[D.inv[c]!]!
    Z.any (fun j => D.El[j]! == w) && !(w == oneR) && !(w == t0R)

@[expose] def findOrder3 (D : EnumData) : ℕ :=
  ((List.range D.El.size).find? fun i => !(D.El[i]! == oneR) &&
    mulR (mulR D.El[i]! D.El[i]!) D.El[i]! == oneR).getD 0

@[expose] def d4BCheck : Bool :=
  let D := mkEnum cGens
  let c3 := findOrder3 D
  let P2 := twoSet D c3
  d4BCheckOn D c3 P2 (zSet D P2)

end CFSG.LargeExtraspecial.S63
