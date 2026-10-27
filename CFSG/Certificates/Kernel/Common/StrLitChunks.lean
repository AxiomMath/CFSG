module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import CFSG.Certificates.Kernel.Common.Tab
meta import all Lean.Shell
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.Tab
public import Lean.Exception

open Lean Elab Command

namespace CFSG.KC.StrLitChunks

meta partial def strLits (e : Expr) : List String :=
  match e with
  | .lit (.strVal s) => [s]
  | .app f a => strLits f ++ strLits a
  | .lam _ t b _ => strLits t ++ strLits b
  | .forallE _ t b _ => strLits t ++ strLits b
  | .letE _ t v b _ => strLits t ++ strLits v ++ strLits b
  | .mdata _ b => strLits b
  | .proj _ _ b => strLits b
  | _ => []

meta def addDeclDeep (mb : Nat) (x : CoreM Unit) : CoreM Unit := do
  let ctx ← read
  let s ← get
  Lean.Internal.setThreadStackSize (USize.ofNat (mb * 1024 * 1024))
  let t ← IO.asTask (prio := .dedicated) (x.toIO ctx s)
  let r ← IO.wait t
  Lean.Internal.setThreadStackSize (USize.ofNat (8 * 1024 * 1024))
  match r with
  | .ok ((), s') => set s'
  | .error e => throwError m!"{e}"

end CFSG.KC.StrLitChunks

open CFSG.KC.Tab CFSG.KC.StrLitChunks in
elab "#str_lit_chunks " pre:ident cId:ident kN:num depth:num stackMB:num : command => do
  let P := pre.getId
  let cN ← liftCoreM <| realizeGlobalConstNoOverload cId
  let some v := ((← getEnv).find? cN).bind ConstantInfo.value?
    | throwError "#str_lit_chunks: {cN} has no value"
  let s ← match (strLits v).eraseDups with
    | [s] => pure s
    | _ => throwError "#str_lit_chunks: {cN} does not contain exactly one string literal"
  let k := kN.getNat
  if k == 0 then throwError "#str_lit_chunks: the chunk size is 0"
  let cs := s.toList.toArray
  let n := max 1 ((cs.size + k - 1) / k)
  let charE : Expr := mkConst ``Char
  let lty := mkApp (mkConst ``List [0]) charE
  let consC := mkApp (mkConst ``List.cons [0]) charE
  let nilC := mkApp (mkConst ``List.nil [0]) charE
  let app ← liftTermElabM do
    let e ← Term.elabTerm (← `(fun (a b : List Char) => a ++ b)) none
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let mut chE : Std.HashMap Nat Expr := {}
  for c in cs do
    unless chE.contains c.toNat do
      chE := chE.insert c.toNat (mkApp (mkConst ``Char.ofNat) (mkRawNatLit c.toNat))
  let cName := fun (j : Nat) => P ++ Name.mkSimple s!"c{j}"
  let strE := mkConst ``String
  withSync do
    for j in [0:n] do
      let lo := j * k
      let hi := min cs.size (lo + k)
      let mut acc := nilC
      for i' in [0:hi - lo] do
        acc := mkApp2 consC chE[cs[hi - 1 - i']!.toNat]! acc
      addDef (cName j) lty acc
    addDef (P ++ `n) natT (lit n)
    let mut t := mkConst (cName (n - 1))
    for j' in [1:n] do
      t := (mkApp2 app (mkConst (cName (n - 1 - j'))) t).headBeta
    addDef (P ++ `chars) lty t
    let litE := Expr.lit (.strVal s)
    let ty := mkApp3 (mkConst ``Eq [1]) strE litE
      (mkApp (mkConst ``String.ofList) (mkConst (P ++ `chars)))
    let pf := mkApp2 (mkConst ``Eq.refl [1]) strE litE
    addDeclDeep stackMB.getNat <| withOptions (maxRecDepth.set · depth.getNat) do
      CFSG.KC.addThmDecl <| { name := P ++ `eq, levelParams := [], type := ty, value := pf }
