module

public meta import Lean
public import CFSG.Certificates.Kernel.Common.Harness
meta import all CFSG.Certificates.Kernel.Common.Harness

open Lean Elab Command

namespace CFSG.KC.NatItemsRaw

meta def items (b : ByteArray) : Except String (Array Nat) := do
  let mut out := #[]
  let mut i := 0
  while i < b.size do
    if b.size < i + 4 then throw "truncated item header"
    let n := CFSG.KC.Load.natLE b i (i + 4)
    if b.size < i + 4 + n then throw "truncated item"
    out := out.push (CFSG.KC.Load.natLE b (i + 4) (i + 4 + n))
    i := i + 4 + n
  return out

end CFSG.KC.NatItemsRaw

declare_syntax_cat kcNatItem
syntax ident : kcNatItem
syntax ident noWs "[" noWs num noWs "]" : kcNatItem
syntax ident noWs "[" noWs "]" : kcNatItem
syntax "(" ident num num ")" : kcNatItem

open CFSG.KC.Load CFSG.KC.NatItemsRaw in
elab "#kc_nat_items " pre:ident path:str size:num hash:num es:kcNatItem* : command => do
  let b ← readPinned path.getString size.getNat hash.getNat
  let vs ← match items b with
    | .ok vs => pure vs
    | .error e => throwError "#kc_nat_items: {path.getString}: {e}"
  let take (pos : Nat) : CommandElabM Nat := do
    let some v := vs[pos]? | throwError "#kc_nat_items: {path.getString} has too few items"
    return v
  let mut pos := 0
  let mut defs : Array (Name × Expr × Expr) := #[]
  for e in es do
    match e with
    | `(kcNatItem| $x:ident) =>
      defs := defs.push (pre.getId ++ x.getId, natE, mkRawNatLit (← take pos))
      pos := pos + 1
    | `(kcNatItem| $x:ident[$k:num]) =>
      for j in [0:k.getNat] do
        defs := defs.push ((pre.getId ++ x.getId).appendAfter s!"{j}", natE,
          mkRawNatLit (← take (pos + j)))
      pos := pos + k.getNat
    | `(kcNatItem| ($x:ident $a:num $c:num)) =>
      for j in [a.getNat:c.getNat] do
        defs := defs.push ((pre.getId ++ x.getId).appendAfter s!"{j}", natE,
          mkRawNatLit (← take (pos + (j - a.getNat))))
      pos := pos + (c.getNat - a.getNat)
    | `(kcNatItem| $x:ident[]) =>
      let c ← take pos
      let mut xs : Array Expr := #[]
      for j in [0:c] do
        xs := xs.push (mkRawNatLit (← take (pos + 1 + j)))
      defs := defs.push (pre.getId ++ x.getId, listNatE, mkNatList xs)
      pos := pos + 1 + c
    | _ => throwError "#kc_nat_items: bad entry"
  unless pos == vs.size do
    throwError "#kc_nat_items: {path.getString} has {vs.size} items, the entries take {pos}"
  withSync do
    for (n, ty, v) in defs do
      addDef n ty v true
