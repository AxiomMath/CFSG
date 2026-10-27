module

public import CFSG.LargeExtraspecial.S63CD4Inputs
public meta import CFSG.LargeExtraspecial.S63CD4Inputs

public section

namespace CFSG.LargeExtraspecial.S63

open CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native

@[expose] def pickSpan (n : ℕ) (f : ℕ → Array ℕ) (z : Array ℕ) (target : ℕ) : List ℕ := Id.run do
  let mut S : Std.HashSet (Array ℕ) := (({} : Std.HashSet (Array ℕ)).insert oneR).insert z
  let mut els : Array (Array ℕ) := #[oneR, z]
  let mut picks : Array ℕ := #[]
  for c in [0:n] do
    if els.size ≥ target then break
    let y := f c
    if !S.contains y then
      let new := els.map (mulR y)
      for e in new do
        S := S.insert e
      els := els ++ new
      picks := picks.push c
  return picks.toList

@[expose] def irrList (L : EnumData) (ls : List ℕ) (x : Array ℕ) : List (Array ℕ) :=
  (ls.map fun c => conjI L.El[c]! L.El[L.inv[c]!]! x) ++ [z0R]

@[expose] def commList (Q L : EnumData) (ps : List (ℕ × ℕ)) : List (Array ℕ) :=
  (ps.map fun p => commI Q.El[p.1]! Q.El[Q.inv[p.1]!]! L.El[p.2]! L.El[L.inv[p.2]!]!) ++ [z0R]

@[expose] def d4ACheckOn (Q L : EnumData) (irr : ℕ → List ℕ) (comms : List (ℕ × ℕ)) : Bool :=
  gensOK qGens && gensOK lGens && Q.ok qGens 512 && Q.invOK 512 && L.ok lGens 504 &&
  L.invOK 504 &&
  (allLt qGens.size fun k => mulR qGens[k]! z0R == mulR z0R qGens[k]!) &&
  (allLt lGens.size fun k => mulR lGens[k]! z0R == mulR z0R lGens[k]!) &&
  memR Q.El Q.idx z0R &&
  (allLt 504 fun i => L.El[i]! == oneR || !memR Q.El Q.idx L.El[i]!) &&
  (allLt lGens.size fun k => allLt 512 fun i => memR Q.El Q.idx (conjR lGens[k]! Q.El[i]!)) &&
  (allLt 504 fun i => !(mulR L.El[i]! L.El[i]! == oneR) || L.El[i]! == oneR ||
    (List.range 504).any fun c =>
      let m := mulR L.El[i]! (conjI L.El[c]! L.El[L.inv[c]!]! L.El[i]!)
      !(m == oneR) && powRows 24 m 63 == oneR) &&
  (allLt 512 fun j => Q.El[j]! == oneR || Q.El[j]! == z0R ||
    (let ls := irr j
     ls.all (fun c => decide (c < 504)) &&
       coverOK Q.El Q.idx (subProds (irrList L ls Q.El[j]!)))) &&
  (comms.all (fun p => decide (p.1 < 512) && decide (p.2 < 504)) &&
    coverOK Q.El Q.idx (subProds (commList Q L comms))) &&
  (allLt 512 fun i => allLt qGens.size fun k =>
    conjI Q.El[i]! Q.El[Q.inv[i]!]! qGens[k]! == qGens[k]! ||
      conjI Q.El[i]! Q.El[Q.inv[i]!]! qGens[k]! == mulR qGens[k]! z0R) &&
  (allLt 504 fun i => L.El[i]! == oneR || (List.range qGens.size).any fun k =>
    !(conjI L.El[i]! L.El[L.inv[i]!]! qGens[k]! == qGens[k]!) &&
      !(conjI L.El[i]! L.El[L.inv[i]!]! qGens[k]! == mulR qGens[k]! z0R))

@[expose] def irrChoice (Q L : EnumData) (j : ℕ) : List ℕ :=
  pickSpan 504 (fun c => conjI L.El[c]! L.El[L.inv[c]!]! Q.El[j]!) z0R 512

@[expose] def commChoice (Q L : EnumData) : List (ℕ × ℕ) :=
  (pickSpan (512 * 504) (fun c => commI Q.El[c / 504]! Q.El[Q.inv[c / 504]!]! L.El[c % 504]!
    L.El[L.inv[c % 504]!]!) z0R 512).map fun c => (c / 504, c % 504)

@[expose] def d4ACheck : Bool :=
  let Q := mkEnum qGens
  let L := mkEnum lGens
  d4ACheckOn Q L (irrChoice Q L) (commChoice Q L)

end CFSG.LargeExtraspecial.S63
