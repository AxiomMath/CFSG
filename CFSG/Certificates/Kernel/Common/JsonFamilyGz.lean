module

public meta import Lean
public import CFSG.Certificates.Kernel.Common.JsonGz
meta import all CFSG.Certificates.Kernel.Common.Harness
meta import all CFSG.Certificates.Kernel.Common.HarnessGz
meta import all CFSG.Certificates.Kernel.Common.JsonGz

open Lean Elab Command Meta

open CFSG.KC.Load CFSG.KC.Gz CFSG.KC.JsonGz in
elab "#kc_json_family_gz " pre:ident path:str size:num hash:num
    fs:("(" ident " : " term ")")* : command => do
  let b ← readPinnedGz path.getString size.getNat hash.getNat
  let some s := String.fromUTF8? b | throwError "#kc_json_family_gz: {path.getString} is not UTF-8"
  let j ← match Json.parse s with
    | .ok j => pure j
    | .error e => throwError "#kc_json_family_gz: {path.getString}: {e}"
  let fields := fs.map fun f => ((⟨f.raw[1]⟩ : Ident), (⟨f.raw[3]⟩ : Term))
  let defs ← liftTermElabM do
    let mut out := #[]
    for (x, t) in fields do
      let ty ← instantiateMVars (← Term.elabType t)
      let .ok (.arr vs) := j.getObjVal? x.getId.toString
        | throwError "#kc_json_family_gz: member {x.getId} is not an array"
      for (v, k) in vs.toList.zipIdx do
        out := out.push ((pre.getId ++ x.getId).appendAfter s!"{k}", ty, ← ofJson ty v)
    return out
  withSync do
    for (n, ty, v) in defs do
      addDef n ty v true
