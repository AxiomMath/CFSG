module

public meta import Lean
public import CFSG.Certificates.Kernel.Common.NatItemsGz
meta import all CFSG.Certificates.Kernel.Common.Harness
meta import all CFSG.Certificates.Kernel.Common.HarnessGz
meta import all CFSG.Certificates.Kernel.Common.NatItemsGz

open Lean Elab Command

declare_syntax_cat kcNatRun
syntax "(" ident num num ")" : kcNatRun
syntax "(" ident num num ")" noWs "[" noWs "]" : kcNatRun

open CFSG.KC.Load CFSG.KC.Gz CFSG.KC.NatItems in
elab "#kc_nat_runs_gz " pre:ident path:str size:num hash:num es:kcNatRun* : command => do
  let b ← readPinnedGz path.getString size.getNat hash.getNat
  let vs ← match items b with
    | .ok vs => pure vs
    | .error e => throwError "#kc_nat_runs_gz: {path.getString}: {e}"
  let take (pos : Nat) : CommandElabM Nat := do
    let some v := vs[pos]? | throwError "#kc_nat_runs_gz: {path.getString} has too few items"
    return v
  let mut pos := 0
  let mut defs : Array (Name × Expr × Expr) := #[]
  for e in es do
    match e with
    | `(kcNatRun| ($x:ident $a:num $c:num)) =>
      for j in [a.getNat:c.getNat] do
        defs := defs.push ((pre.getId ++ x.getId).appendAfter s!"{j}", natE, mkRawNatLit (← take pos))
        pos := pos + 1
    | `(kcNatRun| ($x:ident $a:num $c:num)[]) =>
      for j in [a.getNat:c.getNat] do
        let n ← take pos
        let mut xs : Array Expr := #[]
        for i in [0:n] do
          xs := xs.push (mkRawNatLit (← take (pos + 1 + i)))
        defs := defs.push ((pre.getId ++ x.getId).appendAfter s!"{j}", listNatE, mkNatList xs)
        pos := pos + 1 + n
    | _ => throwError "#kc_nat_runs_gz: bad entry"
  unless pos == vs.size do
    throwError "#kc_nat_runs_gz: {path.getString} has {vs.size} items, the entries take {pos}"
  withSync do
    for (n, ty, v) in defs do
      addDef n ty v true
