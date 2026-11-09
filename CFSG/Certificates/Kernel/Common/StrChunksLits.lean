module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import CFSG.Certificates.Kernel.Common.Tab
meta import all Lean.Shell
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.Tab
public import Lean.Exception

open Lean Elab Command

public section

namespace CFSG.KC.StrChunksLits

theorem ofList_glue {s t : String} {a b : List Char} (h₁ : s = String.ofList a)
    (h₂ : t = String.ofList b) : s ++ t = String.ofList (a ++ b) := by
  rw [h₁, h₂, String.ofList_append]

end CFSG.KC.StrChunksLits

end

namespace CFSG.KC.StrChunksLits

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

meta partial def litChain (e : Expr) (ls : Array String := #[]) (ts : Array Expr := #[]) :
    Option (Array String × Array Expr) :=
  match e with
  | .lit (.strVal s) => some (ls.push s, ts.push e)
  | _ =>
    if e.isAppOfArity ``HAppend.hAppend 6 then
      match e.getArg! 4 with
      | .lit (.strVal s) => litChain (e.getArg! 5) (ls.push s) (ts.push e)
      | _ => none
    else none

end CFSG.KC.StrChunksLits

open CFSG.KC.Tab CFSG.KC.StrChunksLits in
elab "#str_chunks_lits " pre:ident sId:ident depth:num stackMB:num : command => do
  let P := pre.getId
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let some v := ((← getEnv).find? sN).bind ConstantInfo.value?
    | throwError "#str_chunks_lits: {sN} has no value"
  let some (ls, ts) := litChain v
    | throwError "#str_chunks_lits: {sN} is not an append chain of string literals"
  let n := ls.size
  let charE : Expr := mkConst ``Char
  let lty := mkApp (mkConst ``List [0]) charE
  let consC := mkApp (mkConst ``List.cons [0]) charE
  let nilC := mkApp (mkConst ``List.nil [0]) charE
  let strE := mkConst ``String
  let app ← liftTermElabM do
    let e ← Term.elabTerm (← `(fun (a b : List Char) => a ++ b)) none
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let mut chE : Std.HashMap Nat Expr := {}
  for l in ls do
    for c in l.toList do
      unless chE.contains c.toNat do
        chE := chE.insert c.toNat (mkApp (mkConst ``Char.ofNat) (mkRawNatLit c.toNat))
  let cN := fun (j : Nat) => P ++ Name.mkSimple s!"c{j}"
  let eN := fun (j : Nat) => P ++ Name.mkSimple s!"e{j}"
  let eqE := fun (ty a b : Expr) => mkApp3 (mkConst ``Eq [1]) ty a b
  let ofL := fun x => mkApp (mkConst ``String.ofList) x
  let thmV := fun (name : Name) (type value : Expr) =>
    CFSG.KC.addThmDecl ({ name := name, levelParams := [], type := type, value := value } : TheoremVal)
  let deep := fun (x : CoreM Unit) =>
    addDeclDeep stackMB.getNat <| withOptions (maxRecDepth.set · depth.getNat) x
  withSync do
    for j in [0:n] do
      let cs := ls[j]!.toList.toArray
      let mut acc := nilC
      for i' in [0:cs.size] do
        acc := mkApp2 consC chE[cs[cs.size - 1 - i']!.toNat]! acc
      addDef (cN j) lty acc
    addDef (P ++ `n) natT (lit n)
    let mut t := mkConst (cN (n - 1))
    let mut rs : Array Expr := #[t]
    for j' in [1:n] do
      t := (mkApp2 app (mkConst (cN (n - 1 - j'))) t).headBeta
      rs := rs.push t
    rs := rs.reverse
    addDef (P ++ `chars) lty t
    for j in [0:n] do
      let l := mkStrLit ls[j]!
      deep <| thmV (eN j) (eqE strE l (ofL (mkConst (cN j)))) (mkApp2 (mkConst ``Eq.refl [1]) strE l)
    let mut pf := mkConst (eN (n - 1))
    for j' in [1:n] do
      let j := n - 1 - j'
      pf := mkAppN (mkConst ``ofList_glue)
        #[mkStrLit ls[j]!, ts[j + 1]!, mkConst (cN j), rs[j + 1]!, mkConst (eN j), pf]
    thmV (P ++ `eq) (eqE strE (mkConst sN) (ofL (mkConst (P ++ `chars)))) pf
