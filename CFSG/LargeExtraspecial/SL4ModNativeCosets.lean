module

public import CFSG.LargeExtraspecial.SL4ModNativeBasic

public section

namespace CFSG.LargeExtraspecial.SL4Mod.Native

set_option compiler.extract_closed false

@[expose] def inPj (j : Nat) (A : Array Nat) : Bool :=
  (List.range 4).all fun r => (List.range r).all fun c =>
    (r == j + 1 && c == j) || !((A[r]?.getD 0).testBit c)

structure CosetData where
  words : Array (List Nat)
  codes : Array (Array Nat)
  invs : Array (Array Nat)
  tau : Array (Array Nat)
  fac : Array (Array (Bool × Nat × Nat))
deriving Inhabited

@[expose] def findCoset (j : Nat) (invs : Array (Array Nat)) (g : Array Nat) : Option Nat :=
  (List.range invs.size).find? fun k => inPj j (mul4 invs[k]! g)

@[expose] def cosetBFS (j : Nat) : Array (List Nat) × Array (Array Nat) × Array (Array Nat) :=
  Id.run do
    let mut words : Array (List Nat) := #[[]]
    let mut codes : Array (Array Nat) := #[id4]
    let mut invs : Array (Array Nat) := #[id4]
    let mut q := 0
    for _ in [0:200] do
      if q < codes.size then
        for s in [0:6] do
          let g := mul4 (genCode s) codes[q]!
          if (findCoset j invs g).isNone then
            words := words.push (s :: words[q]!)
            codes := codes.push g
            invs := invs.push (mul4 invs[q]! (genCode s))
        q := q + 1
    return (words, codes, invs)

@[expose] def facCode (j : Nat) (f : Bool) (e₁ e₂ : Nat) : Array Nat :=
  if f then mul4 (mul4 (uCode e₁) (genCode (j + 3))) (uCode e₂) else uCode e₁

@[expose] def bigCell (j : Nat) : Array (Array Nat) :=
  Array.ofFn (n := 4096) fun t => facCode j true (t.val / 64) (t.val % 64)

@[expose] def factorP (cell : Array (Array Nat)) (c : Array Nat) : Bool × Nat × Nat :=
  if isUCode c then (false, uDecC c, 0)
  else match cell.findIdx? (· == c) with
    | some t => (true, t / 64, t % 64)
    | none => (false, 0, 0)

@[expose] def cosetData (j : Nat) : CosetData :=
  let (words, codes, invs) := cosetBFS j
  let tau := Array.ofFn (n := 6) fun s =>
    Array.ofFn (n := 105) fun k =>
      (findCoset j invs (mul4 (genCode s.val) codes[k.val]!)).getD 0
  let cell := bigCell j
  let fac := Array.ofFn (n := 6) fun s =>
    Array.ofFn (n := 105) fun k =>
      factorP cell
        (mul4 (mul4 invs[k.val]! (genCode s.val)) codes[tau[s.val]![k.val]! % 105]!)
  { words, codes, invs, tau, fac }

@[expose] def checkTau (j : Nat) (d : CosetData) : Bool :=
  (List.range 6).all fun s => (List.range 105).all fun k =>
    let p := d.fac[s]![k]!
    mul4 (genCode s) (wordCode d.words[d.tau[s]![k]! % 105]!) ==
      mul4 (wordCode d.words[k]!) (facCode j p.1 p.2.1 p.2.2)

end CFSG.LargeExtraspecial.SL4Mod.Native
