module

import all Certificates.Data.Census
public import Certificates.Data.Census

public section

namespace Certificates.GilmanCensusK

open Certificates.Census Std

@[expose] def ixLoop (R : Array IVec) (N : Nat) : HashMap IVec Nat := Id.run do
  let mut ix : HashMap IVec Nat := {}
  for i in [0:N] do ix := ix.insert R[i]! i
  return ix

@[expose] def hsLoop (H : Array (Array Nat)) : HashSet (Array Nat) := Id.run do
  let mut hs : HashSet (Array Nat) := {}
  for h in H do
    for s in [1, 2] do
      hs := hs.insert (h.map fun x => x * s % 3)
  return hs

@[expose] def fhOkLoop (F H : Array (Array Nat)) (G : Array (Array Int)) (N : Nat) (ok : Bool) :
    Bool := Id.run do
  let mut ok := ok
  for i in [0:N] do
    for j in [0:N] do
      if (dot3 F[i]! H[j]! : Int) != (2 * G[i]![j]! / G[j]![j]!) % 3 then ok := false
  return ok

@[expose] def reflLoop (n N : Nat) (R : Array IVec) (G : Array (Array Int)) (ix : HashMap IVec Nat)
    (ok : Bool) : Bool × Array (Array Nat) := Id.run do
  let mut ok := ok
  let mut refl : Array (Array Nat) := #[]
  for i in [0:N] do
    let r := R[i]!
    let mut row : Array Nat := #[]
    for j in [0:N] do
      let s := R[j]!
      let a := 2 * G[j]![i]!
      let b := G[i]![i]!
      if a % b != 0 then ok := false
      let q := a / b
      let z : IVec := Array.ofFn (n := n) fun t => s[t.val]! - q * r[t.val]!
      let neg := (z.find? (· != 0)).getD 0 < 0
      let z := if neg then z.map (- ·) else z
      match ix[z]? with
      | some k => row := row.push k
      | none => ok := false; row := row.push 0
    refl := refl.push row
  return (ok, refl)

@[expose] def tailS (mode n : Nat) (AR : Array IVec) (rho : Array Nat) (B : Array (Array Int))
    (ok : Bool) (R : Array IVec) (absidx F H : Array (Array Nat)) (d : Nat) : Option Data := Id.run do
  let mut ok := ok
  let N := R.size
  let ix := ixLoop R N
  let aix := ixLoop AR AR.size
  if !(F.all fun f => f.any (· != 0)) then ok := false
  let hs := hsLoop H
  if hs.size != 2 * N then ok := false
  let G : Array (Array Int) := R.map fun r => R.map fun s => gramB B r s
  ok := fhOkLoop F H G N ok
  let adj : Array Nat := Array.ofFn (n := N) fun i =>
    (List.range N).foldl (fun m j => if G[i.val]![j]! != 0 then m ||| bit j else m) 0
  let aadj : Array Nat := Array.ofFn (n := AR.size) fun i =>
    (List.range AR.size).foldl
      (fun m j => if gramB B AR[i.val]! AR[j]! != 0 then m ||| bit j else m) 0
  let rf := reflLoop n N R G ix ok
  let all : Array (Array Nat) :=
    Array.ofFn (n := 3 ^ d) fun k => Array.ofFn (n := d) fun i => (k.val / 3 ^ (d - 1 - i.val)) % 3
  let lines := all.filter fun v => firstNZ v == 1
  let full := (1 <<< N) - 1
  let refl := rf.2
  if !rf.1 then return none
  return some { mode, n, d, N, AR, rho, R, absidx, F, H, ix, aix, G, adj, aadj, refl, lines, full }

@[expose] def fhLoop (mode n : Nat) (A B : Array (Array Int)) (sc : Array Int) (emb : Array (Array Nat))
    (AR : Array IVec) : Bool × Array (Array Nat) × Array (Array Nat) := Id.run do
  let mut ok := true
  let mut F : Array (Array Nat) := #[]
  let mut H : Array (Array Nat) := #[]
  for r in AR do
    let norm := gramB B r r
    let h : IVec := Array.ofFn (n := n) fun i => 2 * r[i.val]! * sc[i.val]! / norm
    let f : IVec :=
      if mode == 2 || mode == 3 then r
      else Array.ofFn (n := n) fun j => Id.run do
        let mut t : Int := 0
        for i in [0:n] do
          t := t + r[i]! * A[i]![j.val]!
        return t
    let hv : Array Nat :=
      if mode == 2 || mode == 3 then
        Array.ofFn (n := n) fun i => Id.run do
          let mut t : Int := 0
          for j in [0:n] do
            t := t + A[i.val]![j]! * h[j]!
          return imod3 t
      else h.map imod3
    F := F.push (emb.map fun v => imod3 (dotI f (v.map (fun (x : Nat) => (x : Int)))))
    match coordsIn emb hv n with
    | some c => H := H.push c
    | none => ok := false
  return (ok, F, H)

@[expose] def embLoop (mode n : Nat) (A : Array (Array Int)) : Array (Array Nat) :=
  if mode == 3 then Id.run do
    let mut e : Array (Array Nat) := #[]
    for i in [0:n] do
      let c : Array Nat := Array.ofFn (n := n) fun j => imod3 A[j.val]![i]!
      if rank3 (e.push c) n > e.size then e := e.push c
    return e
  else Array.ofFn (n := n) fun i => Array.ofFn (n := n) fun j => if i.val == j.val then 1 else 0

@[expose] def grpLoop (n : Nat) (AR : Array IVec) (rho : Array Nat) :
    HashMap IVec (Array Nat) × Array IVec := Id.run do
  let mut groups : HashMap IVec (Array Nat) := {}
  let mut keys : Array IVec := #[]
  for i in [0:AR.size] do
    let r := AR[i]!
    let rr : IVec := Array.ofFn (n := n) fun j => r[j.val]! + r[rho[j.val]!]!
    if !groups.contains rr then keys := keys.push rr
    groups := groups.insert rr ((groups.getD rr #[]).push i)
  return (groups, keys)

@[expose] def relLoop (n : Nat) (A : Array (Array Int)) (AR : Array IVec)
    (groups : HashMap IVec (Array Nat)) (R : Array IVec) :
    Array (Array Nat) × Array (Array Nat) × Array (Array Nat) := Id.run do
  let emb : Array (Array Nat) :=
    #[#[1, 0, 0, 0, 0, 1], #[0, 0, 1, 0, 1, 0], #[0, 1, 0, 0, 0, 0], #[0, 0, 0, 1, 0, 0]]
  let mut absidx : Array (Array Nat) := #[]
  let mut F : Array (Array Nat) := #[]
  let mut H : Array (Array Nat) := #[]
  for rr in R do
    let grp := groups.getD rr #[]
    absidx := absidx.push grp
    let r := AR[grp[0]!]!
    F := F.push (emb.map fun v => Id.run do
      let mut t : Int := 0
      for i in [0:n] do
        for j in [0:n] do
          t := t + r[i]! * A[i]![j]! * ((v[j]! : Nat) : Int)
      return imod3 t)
    let hv := if grp.size == 2 then rr else r
    H := H.push #[imod3 hv[0]!, imod3 hv[2]!, imod3 hv[1]!, imod3 hv[3]!]
  return (absidx, F, H)

end Certificates.GilmanCensusK

end
