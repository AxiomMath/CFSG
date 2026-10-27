module

public import CFSG.LargeExtraspecial.SL4ModNativeCosets

public section

namespace CFSG.LargeExtraspecial.SL4Mod.Native

open CFSG.Sporadic.SmallF2.Native

set_option compiler.extract_closed false

@[expose] def actV (t : Array Nat) (x : Nat) : Nat :=
  ofBits 105 fun k => x.testBit (t[k]! % 105)

@[expose] def xorSel (mask : Nat) (L : Array Nat) : Nat :=
  (List.range L.size).foldl (fun acc t => if mask.testBit t then acc ^^^ L[t]! else acc) 0

@[expose] def nz (x : Nat) : Bool := (x &&& (2 ^ 105 - 1)) != 0

@[expose] def inSpan (x : Nat) (B : Array Nat) : Bool :=
  (List.range (2 ^ B.size)).any fun mask => xorSel mask B == x

@[expose] def indep9 (L : Array Nat) : Bool :=
  (List.range 512).all fun mask => mask == 0 || nz (xorSel mask L)

@[expose] def derivOK (taus : Array (Array Nat)) (m : Nat) (L : Array Nat)
    (src : Array (Nat × Nat)) : Bool :=
  L[0]! == m && (List.range L.size).all fun t => t == 0 ||
    (decide (src[t]!.1 < 6) && decide (src[t]!.2 < t) &&
      L[t]! == actV taus[src[t]!.1]! L[src[t]!.2]!)

@[expose] def closedOK (taus : Array (Array Nat)) (B : Array Nat) : Bool :=
  (List.range B.size).all fun t => (List.range 6).all fun s => inSpan (actV taus[s]! B[t]!) B

structure SpinCert where
  L : Array Nat
  src : Array (Nat × Nat)
  big : Bool
  sel : Nat
  B : Array Nat
deriving Inhabited

@[expose] def valid (taus : Array (Array Nat)) (m : Nat) (c : SpinCert) : Bool :=
  derivOK taus m c.L c.src &&
    (if c.big then decide (9 ≤ c.L.size) && indep9 c.L
    else nz (xorSel c.sel c.L) && decide (c.B.size ≤ 7) && inSpan (xorSel c.sel c.L) c.B &&
      closedOK taus c.B)

@[expose] def reduceV (basis : Array Nat) (w : Nat) : Nat :=
  basis.foldl (fun v b => min v (v ^^^ b)) w

@[expose] def spinBFS (taus : Array (Array Nat)) (m cap : Nat) : Array Nat × Array (Nat × Nat) :=
  Id.run do
    let mut L : Array Nat := #[m]
    let mut src : Array (Nat × Nat) := #[(0, 0)]
    let mut basis : Array Nat := if m == 0 then #[] else #[m]
    let mut q := 0
    for _ in [0:cap + 1] do
      if q < L.size && L.size < cap then
        for s in [0:6] do
          if L.size < cap then
            let w := actV taus[s]! L[q]!
            let r := reduceV basis w
            if r != 0 then
              L := L.push w
              src := src.push (s, q)
              basis := basis.push r
        q := q + 1
    return (L, src)

@[expose] def spinGen (taus : Array (Array Nat)) (m : Nat) : SpinCert :=
  let (L, src) := spinBFS taus m 9
  if 9 ≤ L.size then { L, src, big := true, sel := 0, B := #[] }
  else if L.size ≤ 7 then { L, src, big := false, sel := 1, B := L }
  else
    match (List.range 256).find? (fun S => S != 0 &&
        decide ((spinBFS taus (xorSel S L) 9).1.size ≤ 7)) with
    | some S => { L, src, big := false, sel := S, B := (spinBFS taus (xorSel S L) 9).1 }
    | none => { L, src, big := false, sel := 0, B := #[] }

structure OrbData where
  par : Array Nat
  lab : Array Nat
  orep : Array Nat
deriving Inhabited

@[expose] def orbGens (i : Nat) : List Nat := [0, 1, 2, i + 3]

@[expose] def orbSweep (d : CosetData) (i t : Nat) (st : Array Nat × Array Nat) :
    Array Nat × Array Nat :=
  (List.range 105).foldl (fun (st : Array Nat × Array Nat) l =>
    if st.2[l]! != 7 then st
    else match (orbGens i).find? (fun s => st.2[d.tau[s]![l]! % 105]! == t) with
      | some s => (st.1.set! l (d.tau[s]![l]! % 105), st.2.set! l t)
      | none => st) st

@[expose] def orbData (d : CosetData) (i : Nat) : OrbData := Id.run do
  let mut par : Array Nat := Array.replicate 105 0
  let mut lab : Array Nat := Array.replicate 105 7
  let mut orep : Array Nat := #[]
  for k0 in [0:105] do
    if lab[k0]! == 7 && orep.size < 7 then
      let t := orep.size
      orep := orep.push k0
      par := par.set! k0 k0
      lab := lab.set! k0 t
      let mut st := (par, lab)
      for _ in [0:105] do
        st := orbSweep d i t st
      par := st.1
      lab := st.2
  return { par, lab, orep }

@[expose] def iterPar (par : Array Nat) : Nat → Nat → Nat
  | 0, k => k
  | n + 1, k => iterPar par n (par[k]! % 105)

@[expose] def checkOrb (d : CosetData) (i : Nat) (od : OrbData) : Bool :=
  (List.range 105).all fun k =>
    (od.par[k]! % 105 == k ||
        (orbGens i).any fun s => od.par[k]! % 105 == d.tau[s]![k]! % 105) &&
      decide (od.lab[k]! < 7) && iterPar od.par 105 k == od.orep[od.lab[k]!]! % 105

@[expose] def expand (od : OrbData) (c : Nat) : Nat :=
  ofBits 105 fun k => c.testBit od.lab[k]!

@[expose] def checkSpin (d : CosetData) (od : OrbData) : Bool :=
  (List.range 128).all fun c => c == 0 || valid d.tau (expand od c) (spinGen d.tau (expand od c))

@[expose] def checkAll : Bool :=
  (List.range 3).all fun j =>
    let d := cosetData j
    checkTau j d && (List.range 3).all fun i =>
      let od := orbData d i
      checkOrb d i od && checkSpin d od

end CFSG.LargeExtraspecial.SL4Mod.Native
