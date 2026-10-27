module

public meta import Lean
public import CFSG.Certificates.Kernel.Common.HarnessGz
meta import all CFSG.Certificates.Kernel.Common.Harness
meta import all CFSG.Certificates.Kernel.Common.HarnessGz

open Lean Elab Command Meta

namespace CFSG.KC.Each

public meta partial def rawLits (e : Expr) : Expr :=
  e.replace fun x =>
    match x with
    | .mdata _ b => some (rawLits b)
    | _ =>
      if x.isAppOfArity ``OfNat.ofNat 3 && (x.getArg! 0).consumeMData.isConstOf ``Nat then
        match (x.getArg! 1).consumeMData with
        | .lit (.natVal n) => some (mkRawNatLit n)
        | _ => none
      else none

public meta def elabCheck (f : Term) (r : Nat) : CommandElabM Expr := liftTermElabM do
  let natT := mkConst ``Nat
  let ty := (List.range r).foldr (fun _ acc => mkForall `a .default natT acc) (mkConst ``Bool)
  let e ← Term.elabTerm f (some ty)
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasMVar || e.hasFVar then throwError "#kc_each: the check is not closed"
  unless ← isDefEq (← inferType e) ty do throwError "#kc_each: the check is not of type {ty}"
  return rawLits e

meta def addCheck (P x : Name) (f : Expr) (i : Nat) (as : Array Nat) : CoreM Unit :=
  CFSG.KC.Load.addTrueThm (P ++ x.appendAfter s!"{i}")
    (mkAppN f ((#[i] ++ as).map mkRawNatLit)).headBeta

meta def rows (b : ByteArray) : Array (Array Nat) :=
  (((String.fromUTF8! b).splitOn "\n").filter (· ≠ "")).toArray.map fun l =>
    ((l.splitOn " ").filter (· ≠ "")).toArray.map String.toNat!

end CFSG.KC.Each

open CFSG.KC.Load CFSG.KC.Each in
elab "#kc_each " pre:ident x:ident f:term:max lo:num hi:num : command => do
  let fE ← elabCheck f 1
  withSync do
    for i in [lo.getNat:hi.getNat] do
      addCheck pre.getId x.getId fE i #[]

open CFSG.KC.Load CFSG.KC.Gz CFSG.KC.Each in
elab "#kc_each_rows " pre:ident x:ident f:term:max path:str size:num hash:num lo:num hi:num :
    command => do
  let b ← readPinnedGz path.getString size.getNat hash.getNat
  let lo := lo.getNat
  let hi := hi.getNat
  let rs := (rows b).filter fun r => lo ≤ r[0]! && r[0]! < hi
  unless rs.map (·[0]!) == (Array.range (hi - lo)).map (lo + ·) do
    throwError "#kc_each_rows: the rows of {path.getString} in [{lo}, {hi}) are not {lo} … {hi - 1}"
  let r := rs[0]!.size
  unless rs.all (·.size == r) do
    throwError "#kc_each_rows: the rows of {path.getString} differ in length"
  let fE ← elabCheck f r
  withSync do
    for row in rs do
      addCheck pre.getId x.getId fE row[0]! (row.extract 1 r)
