module

public meta import Lean
public import CFSG.Certificates.Kernel.Common.HarnessGz
meta import all CFSG.Certificates.Kernel.Common.Harness
meta import all CFSG.Certificates.Kernel.Common.HarnessGz

open Lean Elab Command Meta

namespace CFSG.KC.JsonGzEval

meta partial def natArr (ty : Expr) (j : Json) : MetaM Expr := do
  let ty ← whnfR ty
  if ty.isConstOf ``Nat then
    match j with
    | .num n =>
      unless n.exponent == 0 && n.mantissa ≥ 0 do throwError "expected a natural number, got {j}"
      return mkRawNatLit n.mantissa.toNat
    | _ => throwError "expected a natural number, got {j}"
  let .arr xs := j | throwError "expected an array, got {j}"
  match ty.getAppFnArgs with
  | (``List, #[α]) =>
    let es ← xs.mapM (natArr α)
    return es.foldr (fun e acc => mkApp3 (mkConst ``List.cons [0]) α e acc)
      (mkApp (mkConst ``List.nil [0]) α)
  | (``Array, #[α]) =>
    let es ← xs.mapM (natArr α)
    let l := es.foldr (fun e acc => mkApp3 (mkConst ``List.cons [0]) α e acc)
      (mkApp (mkConst ``List.nil [0]) α)
    return mkApp2 (mkConst ``Array.mk [0]) α l
  | _ => throwError "#kc_json_gz_eval: unsupported type {ty}"

end CFSG.KC.JsonGzEval

open CFSG.KC.Load CFSG.KC.Gz CFSG.KC.JsonGzEval in
elab "#kc_json_gz_eval " pre:ident path:str size:num hash:num fs:("(" ident " : " term ")")* :
    command => do
  let b ← readPinnedGz path.getString size.getNat hash.getNat
  let some s := String.fromUTF8? b | throwError "#kc_json_gz_eval: {path.getString} is not UTF-8"
  let j ← match Json.parse s with
    | .ok j => pure j
    | .error e => throwError "#kc_json_gz_eval: {path.getString}: {e}"
  let fields := fs.map fun f => ((⟨f.raw[1]⟩ : Ident), (⟨f.raw[3]⟩ : Term))
  let defs ← liftTermElabM do
    fields.mapM fun (x, t) => do
      let ty ← instantiateMVars (← Term.elabType t)
      let v ← match j.getObjVal? x.getId.toString with
        | .ok v => pure v
        | .error e => throwError "#kc_json_gz_eval: {e}"
      return (pre.getId ++ x.getId, ty, ← natArr ty v)
  withSync do
    for (n, ty, v) in defs do
      addDef n ty v true
      compileDecls #[n]
