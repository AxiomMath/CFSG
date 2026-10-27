module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm
public import Lean.Exception

open Lean Elab Command Meta

namespace CFSG.KC.EachUnfold

meta partial def natVal? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | .mdata _ b => natVal? b
  | _ =>
    let args := e.getAppArgs
    match e.getAppFn.constName?, args.size with
    | some ``OfNat.ofNat, 3 =>
      if args[0]!.isConstOf ``Nat then natVal? args[1]! else none
    | some ``Nat.succ, 1 => (· + 1) <$> natVal? args[0]!
    | some f, 2 => bin f (natVal? args[0]!) (natVal? args[1]!)
    | some f, 6 =>
      if args[0]!.isConstOf ``Nat && args[1]!.isConstOf ``Nat && args[2]!.isConstOf ``Nat then
        bin (heter f) (natVal? args[4]!) (natVal? args[5]!)
      else none
    | _, _ => none
where
  heter (f : Name) : Name :=
    if f == ``HAdd.hAdd then ``Nat.add else if f == ``HSub.hSub then ``Nat.sub
    else if f == ``HMul.hMul then ``Nat.mul else if f == ``HDiv.hDiv then ``Nat.div
    else if f == ``HMod.hMod then ``Nat.mod else .anonymous
  bin (f : Name) (a b : Option Nat) : Option Nat := do
    let a ← a
    let b ← b
    if f == ``Nat.add then some (a + b) else if f == ``Nat.sub then some (a - b)
    else if f == ``Nat.mul then some (a * b) else if f == ``Nat.div then some (a / b)
    else if f == ``Nat.mod then some (a % b) else if f == ``Nat.min then some (min a b)
    else if f == ``Nat.max then some (max a b) else none

meta def boolVal? (e : Expr) : Option Bool :=
  match e.getAppFn.constName?, e.getAppArgs with
  | some f, #[.lit (.natVal a), .lit (.natVal b)] =>
    if f == ``Nat.beq then some (a == b) else if f == ``Nat.ble then some (a ≤ b)
    else if f == ``Nat.blt then some (a < b) else none
  | _, _ => none

meta def kwhnf (e : Expr) : MetaM Expr := do
  ofExceptKernelException (Kernel.whnf (← getEnv) {} e)

meta partial def literal (e : Expr) : MetaM Expr := do
  let v ← kwhnf e
  if let some n := natVal? v then return mkRawNatLit n
  if v.isAppOfArity ``List.nil 1 then return mkApp (mkConst ``List.nil [0]) (mkConst ``Nat)
  if v.isAppOfArity ``List.cons 3 then
    let some h := natVal? (← kwhnf (v.getArg! 1))
      | throwError "#kc_each_unfold: an element of {e} does not reduce to a literal"
    return mkApp3 (mkConst ``List.cons [0]) (mkConst ``Nat) (mkRawNatLit h) (← literal (v.getArg! 2))
  throwError "#kc_each_unfold: {e} does not reduce to a literal"

meta def fold (gs : Array Name) (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun t => do
    if let some n := natVal? t then
      return .done (mkRawNatLit n)
    if let some b := boolVal? t then
      return .done (mkConst (if b then ``Bool.true else ``Bool.false))
    if t.isAppOfArity ``Bool.rec 4 then
      let c := t.getArg! 3
      if c.isConstOf ``Bool.true then return .done (t.getArg! 2)
      if c.isConstOf ``Bool.false then return .done (t.getArg! 1)
    if let some g := t.getAppFn.constName? then
      if gs.contains g && t.getAppNumArgs == 1 && (t.getArg! 0).isRawNatLit then
        return .done (← literal t)
    return .continue)

meta def addUnfolded (F : Name) (gs : Array Name) (name : Name) (j : Nat) : TermElabM Unit := do
  let some (.defnInfo d) := (← getEnv).find? F
    | throwError "#kc_each_unfold: {F} is not a definition"
  unless d.levelParams.isEmpty do throwError "#kc_each_unfold: {F} has universe parameters"
  withCurrHeartbeats do
    let body ← fold gs (d.value.beta #[mkRawNatLit j])
    if body.hasFVar || body.hasMVar then
      throwError "#kc_each_unfold: the body of {F} is not closed"
    let ty := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) body (mkConst ``Bool.true)
    withOptions (Elab.async.set · false) <|
      CFSG.KC.addThmDecl <| { name, levelParams := [], type := ty, value := reflBoolTrue }

end CFSG.KC.EachUnfold

syntax "#kc_each_unfold " ident num num (" as " ident)? (" at " num)? (" eval" (ppSpace ident)+)? :
  command

syntax "#kc_unfold " ident ident num (" eval" (ppSpace ident)+)? : command

open CFSG.KC.EachUnfold in
elab_rules : command
  | `(#kc_each_unfold $f $lo $hi $[as $p]? $[at $r]? $[eval $gs*]?) => do
    let F ← liftCoreM <| realizeGlobalConstNoOverload f
    let P := (p.map (·.getId)).getD F
    let r0 := (r.map (·.getNat)).getD lo.getNat
    let gNames ← liftCoreM <| (gs.getD #[]).mapM fun i => realizeGlobalConstNoOverload i
    liftTermElabM do
      for k in [lo.getNat:hi.getNat] do
        addUnfolded F gNames (P.appendAfter s!"{k}") (r0 + (k - lo.getNat))
  | `(#kc_unfold $nm $f $j $[eval $gs*]?) => do
    let F ← liftCoreM <| realizeGlobalConstNoOverload f
    let gNames ← liftCoreM <| (gs.getD #[]).mapM fun i => realizeGlobalConstNoOverload i
    liftTermElabM <| addUnfolded F gNames nm.getId j.getNat
