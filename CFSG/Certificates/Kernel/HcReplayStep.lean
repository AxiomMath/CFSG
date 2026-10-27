module

public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Std.Data.HashMap
public import CFSG.Certificates.Kernel.Common.Eval

namespace CFSG.KC.HcPack.Step

open CFSG.KC.Eval

meta def mulM (x g : Nat) : Nat := Id.run do
  let mut r := 0
  for i in [0:32] do
    let gi := (g >>> (5 * i)) % 32
    r := r + (((x >>> (5 * gi)) % 32) <<< (5 * i))
  return r

meta def nats (v : Val) : Except String (Array Nat) :=
  match v with
  | .list xs => xs.mapM fun
    | .nat n => .ok n
    | _ => .error "expected a list of numbers"
  | _ => .error "expected a list"

public meta def bfsRec (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (cap, fuel, a, gsV) ← match args with
    | #[.nat cap, .nat fuel, .nat a, gsV] => pure (cap, fuel, a, gsV)
    | _ => throw "expected cap, fuel, start and generators"
  let gs ← nats gsV
  let mut E : Array Nat := #[a]
  let mut idx : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert a 0
  let mut ds : Array Nat := #[]
  let mut fr : Array Nat := #[a]
  for _ in [0:fuel] do
    if fr.isEmpty then break
    let mut nf : Array Nat := #[]
    for x in fr do
      for g in gs do
        let y := mulM x g
        match idx[y]? with
        | some j => ds := ds.push j
        | none =>
          if E.size < cap then
            ds := ds.push E.size
            idx := idx.insert y E.size
            E := E.push y
            nf := nf.push y
          else throw "a product is new at the cap"
    fr := nf
  let ord := (Array.range E.size).qsort fun i j => E[i]! < E[j]!
  return #[(`E, .list (E.map .nat)), (`ds, .list (ds.map .nat)), (`ord, .list (ord.map .nat))]

end CFSG.KC.HcPack.Step
