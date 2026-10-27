module

public meta import Lean
public import CFSG.Certificates.Kernel.Common.HarnessGz
meta import all CFSG.Certificates.Kernel.Common.Harness
meta import all CFSG.Certificates.Kernel.Common.HarnessGz

open Lean Elab Command Meta

namespace CFSG.KC.JsonGz

meta partial def ofJson (ty : Expr) (j : Json) : MetaM Expr := do
  let ty ← whnfR ty
  if ty.isConstOf ``Nat then
    match j with
    | .num n =>
      unless n.exponent == 0 && n.mantissa ≥ 0 do throwError "expected a natural number, got {j}"
      return mkRawNatLit n.mantissa.toNat
    | _ => throwError "expected a natural number, got {j}"
  if ty.isConstOf ``Bool then
    match j with
    | .bool true => return mkConst ``Bool.true
    | .bool false => return mkConst ``Bool.false
    | _ => throwError "expected a boolean, got {j}"
  match ty.getAppFnArgs with
  | (``List, #[α]) =>
    let .arr xs := j | throwError "expected an array, got {j}"
    let u ← getDecLevel α
    let es ← xs.mapM (ofJson α)
    return es.foldr (fun e acc => mkApp3 (mkConst ``List.cons [u]) α e acc)
      (mkApp (mkConst ``List.nil [u]) α)
  | (``Array, #[α]) =>
    let .arr xs := j | throwError "expected an array, got {j}"
    let u ← getDecLevel α
    let es ← xs.mapM (ofJson α)
    let l := es.foldr (fun e acc => mkApp3 (mkConst ``List.cons [u]) α e acc)
      (mkApp (mkConst ``List.nil [u]) α)
    return mkApp2 (mkConst ``Array.mk [u]) α l
  | (``Prod, #[α, β]) =>
    let .arr xs := j | throwError "expected a pair, got {j}"
    unless xs.size == 2 do throwError "expected a pair, got {j}"
    let u ← getDecLevel α
    let v ← getDecLevel β
    return mkApp4 (mkConst ``Prod.mk [u, v]) α β (← ofJson α xs[0]!) (← ofJson β xs[1]!)
  | _ => throwError "#kc_json_gz: unsupported type {ty}"

end CFSG.KC.JsonGz

open CFSG.KC.Load CFSG.KC.Gz CFSG.KC.JsonGz in
elab "#kc_json_gz " pre:ident path:str size:num hash:num fs:("(" ident " : " term ")")* :
    command => do
  let b ← readPinnedGz path.getString size.getNat hash.getNat
  let some s := String.fromUTF8? b | throwError "#kc_json_gz: {path.getString} is not UTF-8"
  let j ← match Json.parse s with
    | .ok j => pure j
    | .error e => throwError "#kc_json_gz: {path.getString}: {e}"
  let fields := fs.map fun f => ((⟨f.raw[1]⟩ : Ident), (⟨f.raw[3]⟩ : Term))
  let defs ← liftTermElabM do
    fields.mapM fun (x, t) => do
      let ty ← instantiateMVars (← Term.elabType t)
      let v ← match j.getObjVal? x.getId.toString with
        | .ok v => pure v
        | .error e => throwError "#kc_json_gz: {e}"
      return (pre.getId ++ x.getId, ty, ← ofJson ty v)
  withSync do
    for (n, ty, v) in defs do
      addDef n ty v true
