module

public meta import Lean
public import CFSG.Certificates.Kernel.Common.HarnessGz
meta import all CFSG.Certificates.Kernel.Common.Harness
meta import all CFSG.Certificates.Kernel.Common.HarnessGz

open Lean Elab Command Meta

namespace CFSG.KC.JsonGzC

meta def mkListE (u : Level) (α : Expr) (es : Array Expr) : Expr :=
  es.foldr (fun e acc => mkApp3 (mkConst ``List.cons [u]) α e acc) (mkApp (mkConst ``List.nil [u]) α)

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
    return mkListE (← getDecLevel α) α (← xs.mapM (ofJson α))
  | (``Array, #[α]) =>
    let .arr xs := j | throwError "expected an array, got {j}"
    let u ← getDecLevel α
    return mkApp2 (mkConst ``Array.mk [u]) α (mkListE u α (← xs.mapM (ofJson α)))
  | (``Prod, #[α, β]) =>
    let .arr xs := j | throwError "expected a tuple, got {j}"
    unless xs.size ≥ 2 do throwError "expected a tuple, got {j}"
    let u ← getDecLevel α
    let v ← getDecLevel β
    let r := if xs.size == 2 then xs[1]! else .arr (xs.extract 1 xs.size)
    return mkApp4 (mkConst ``Prod.mk [u, v]) α β (← ofJson α xs[0]!) (← ofJson β r)
  | _ =>
    let .const I us := ty.getAppFn | throwError "#kc_jsonc_gz: unsupported type {ty}"
    let .inductInfo ii ← getConstInfo I | throwError "#kc_jsonc_gz: unsupported type {ty}"
    unless ii.numIndices == 0 && ty.getAppNumArgs == ii.numParams do
      throwError "#kc_jsonc_gz: unsupported type {ty}"
    let .arr xs := j | throwError "expected an array, got {j}"
    let (k, fs) ← if isStructure (← getEnv) I then pure ((0 : Nat), xs) else
      match xs[0]? with
      | some (Json.num c) =>
        unless c.exponent == 0 && c.mantissa ≥ 0 do throwError "expected a constructor index, got {j}"
        pure (c.mantissa.toNat, xs.extract 1 xs.size)
      | _ => throwError "expected a constructor index, got {j}"
    let some c := ii.ctors[k]? | throwError "#kc_jsonc_gz: no constructor {k} of {I}"
    let ci ← getConstInfoCtor c
    unless fs.size == ci.numFields do
      throwError "#kc_jsonc_gz: {c} takes {ci.numFields} fields, got {j}"
    let params := ty.getAppArgs
    let mut e := mkAppN (mkConst c us) params
    let mut cty ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams us) params
    for f in fs do
      let .forallE _ d b _ ← whnf cty | throwError "#kc_jsonc_gz: bad constructor type {cty}"
      let v ← ofJson d f
      e := mkApp e v
      cty := b.instantiate1 v
    return e

end CFSG.KC.JsonGzC

open CFSG.KC.Load CFSG.KC.Gz CFSG.KC.JsonGzC in
elab "#kc_jsonc_gz " pre:ident path:str size:num hash:num fs:("(" ident " : " term ")")* :
    command => do
  let b ← readPinnedGz path.getString size.getNat hash.getNat
  let some s := String.fromUTF8? b | throwError "#kc_jsonc_gz: {path.getString} is not UTF-8"
  let j ← match Json.parse s with
    | .ok j => pure j
    | .error e => throwError "#kc_jsonc_gz: {path.getString}: {e}"
  let fields := fs.map fun f => ((⟨f.raw[1]⟩ : Ident), (⟨f.raw[3]⟩ : Term))
  let defs ← liftTermElabM do
    fields.mapM fun (x, t) => do
      let ty ← instantiateMVars (← Term.elabType t)
      let v ← match j.getObjVal? x.getId.toString with
        | .ok v => pure v
        | .error e => throwError "#kc_jsonc_gz: {e}"
      return (pre.getId ++ x.getId, ty, ← ofJson ty v)
  withSync do
    for (n, ty, v) in defs do
      addDef n ty v true
