module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.EachUnfold
meta import all CFSG.Certificates.Kernel.Common.EachUnfold

public section

namespace CFSG.KC.EachUnfold

@[expose] def nameRange (R : Nat → Nat) (a b : Nat) : List Nat :=
  (List.range' a (b - a)).map R

end CFSG.KC.EachUnfold

end

open Lean Elab Command Meta

namespace CFSG.KC.EachUnfold

meta def nameAt (C : Name) (a : Nat) : Expr := mkConst (C.appendAfter s!"{a}")

meta def names (rs : Array (Name × Name)) (e : Expr) : MetaM Expr := do
  let env ← getEnv
  Meta.transform e (post := fun t => do
    let some f := t.getAppFn.constName? | return .continue
    let args := t.getAppArgs
    let rep? : Option Expr ←
      if f == ``nameRange && args.size == 3 then
        match args[0]!.constName?, args[1]!.rawNatLit?, args[2]!.rawNatLit? with
        | some r, some a, some b =>
          match rs.find? (·.1 == r) with
          | some (_, C) =>
            pure <| some <| (List.range' a (b - a)).foldr
              (fun j acc => mkApp3 (mkConst ``List.cons [0]) (mkConst ``Nat) (nameAt C j) acc)
              (mkApp (mkConst ``List.nil [0]) (mkConst ``Nat))
          | none => pure none
        | _, _, _ => pure none
      else if args.size == 1 then
        match rs.find? (·.1 == f), args[0]!.rawNatLit? with
        | some (_, C), some a => pure (some (nameAt C a))
        | _, _ => pure none
      else pure none
    let some rep := rep? | return .continue
    unless ← ofExceptKernelException (Kernel.isDefEq env {} t rep) do
      throwError "#kc_each_unfold_names: {t} is not definitionally {rep}"
    return .done rep)

meta def addUnfoldedNames (F : Name) (gs : Array Name) (rs : Array (Name × Name)) (name : Name)
    (j : Nat) : TermElabM Unit := do
  let some (.defnInfo d) := (← getEnv).find? F
    | throwError "#kc_each_unfold_names: {F} is not a definition"
  unless d.levelParams.isEmpty do throwError "#kc_each_unfold_names: {F} has universe parameters"
  withCurrHeartbeats do
    let body ← names rs (← fold gs (d.value.beta #[mkRawNatLit j]))
    if body.hasFVar || body.hasMVar then
      throwError "#kc_each_unfold_names: the body of {F} is not closed"
    let ty := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) body (mkConst ``Bool.true)
    withOptions (Elab.async.set · false) <|
      CFSG.KC.addThmDecl <| { name, levelParams := [], type := ty, value := reflBoolTrue }

end CFSG.KC.EachUnfold

syntax "#kc_each_unfold_names " ident num num (" as " ident)? (" at " num)?
  (" eval" (ppSpace ident)+)? " names" (ppSpace "(" ident ident ")")+ : command

syntax "#kc_unfold_names " ident ident num (" eval" (ppSpace ident)+)?
  " names" (ppSpace "(" ident ident ")")+ : command

open CFSG.KC.EachUnfold in
elab_rules : command
  | `(#kc_each_unfold_names $f $lo $hi $[as $p]? $[at $r]? $[eval $gs*]? names $[($rs $cs)]*) => do
    let F ← liftCoreM <| realizeGlobalConstNoOverload f
    let P := (p.map (·.getId)).getD F
    let r0 := (r.map (·.getNat)).getD lo.getNat
    let gNames ← liftCoreM <| (gs.getD #[]).mapM fun i => realizeGlobalConstNoOverload i
    let rNames ← liftCoreM <| rs.mapM fun i => realizeGlobalConstNoOverload i
    let pairs := rNames.zip (cs.map (·.getId))
    liftTermElabM do
      for k in [lo.getNat:hi.getNat] do
        addUnfoldedNames F gNames pairs (P.appendAfter s!"{k}") (r0 + (k - lo.getNat))
  | `(#kc_unfold_names $nm $f $j $[eval $gs*]? names $[($rs $cs)]*) => do
    let F ← liftCoreM <| realizeGlobalConstNoOverload f
    let gNames ← liftCoreM <| (gs.getD #[]).mapM fun i => realizeGlobalConstNoOverload i
    let rNames ← liftCoreM <| rs.mapM fun i => realizeGlobalConstNoOverload i
    liftTermElabM <| addUnfoldedNames F gNames (rNames.zip (cs.map (·.getId))) nm.getId j.getNat
