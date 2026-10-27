module

public import CFSG.Certificates.Kernel.Common.ForallChunks
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.Tab

public section

namespace CFSG.KC.GridChunks

universe u

theorem transport {α : Sort u} (M : α → Prop) (a b : α) (e : b = a) (h : M a) : M b := by
  subst e
  exact h

open Lean CFSG.KC.Tab

meta partial def normLits (e : Expr) : Expr :=
  e.replace fun x =>
    match x with
    | .mdata _ b => some (normLits b)
    | _ =>
      if x.isAppOfArity ``OfNat.ofNat 3 && (x.getArg! 0).consumeMData.isConstOf ``Nat then
        match (x.getArg! 1).consumeMData with
        | .lit (.natVal n) => some (mkRawNatLit n)
        | _ => none
      else none

meta def hole (k : Nat) : Expr := mkFVar ⟨.num `_kcGridChunks k⟩

meta partial def diffE (t s : Expr) : StateM (Array (Expr × Expr)) Expr := do
  if t == s then return s
  match t, s with
  | _, .mdata d s' => return .mdata d (← diffE t s')
  | .mdata _ t', _ => diffE t' s
  | .app .., .app .. =>
    let tf := t.getAppFn
    let sf := s.getAppFn
    if tf == sf && !tf.isFVar && t.getAppNumArgs == s.getAppNumArgs then
      let ta := t.getAppArgs
      let sa := s.getAppArgs
      let mut args : Array Expr := #[]
      for i in [0:ta.size] do
        args := args.push (← diffE ta[i]! sa[i]!)
      return mkAppN sf args
    else leaf
  | _, _ => leaf
where
  leaf : StateM (Array (Expr × Expr)) Expr := do
    let k := (← get).size
    modify (·.push (t, s))
    return hole k

meta def idxE (g : Expr) (R : Nat) (r : Expr) : Expr :=
  mkApp2 (mkConst ``Nat.add) (mkApp2 (mkConst ``Nat.mul) g (lit R)) r

meta def forallLt (k : Nat) (body : Expr → Expr) : Expr :=
  mkForall `q .default natT (mkForall `h .default
    (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, lit k])
    (body (mkBVar 1)))

meta def forallChain (Q : Expr) (k : Nat) (thm : Nat → Expr) : Expr := Id.run do
  let mut pf := mkApp (mkConst ``CFSG.KC.ForallChunks.forall_lt_zero) Q
  for s in [0:k] do
    pf := mkAppN (mkConst ``CFSG.KC.ForallChunks.forall_lt_succ) #[Q, lit s, pf, thm s]
  return pf

meta def addTable (F : Name) (vs : Array Nat) : CoreM Unit := do
  let cnt := max vs.size 1
  let h := Nat.log2 (2 * cnt - 1)
  addDef (F ++ `Z) natT (lit 0)
  for k in [0:vs.size] do
    addDef (F ++ Name.mkSimple s!"L{k}") natT (lit vs[k]!)
  let leaf := fun k => constFn (if k < vs.size then mkConst (F ++ Name.mkSimple s!"L{k}")
    else mkConst (F ++ `Z))
  addDef F fnT (table leaf (1 <<< h) 0)

meta def restate (tmpl : Expr) (pairs : Array (Expr × Expr)) (h : Expr) : Expr := Id.run do
  let n := pairs.size
  let holes := (Array.range n).map hole
  let mut h := h
  for i in [0:n] do
    let (s, l) := pairs[i]!
    let α := match l with
      | .lit (.strVal _) => mkConst ``String
      | _ => natT
    let vals := (Array.range n).map fun j =>
      if j < i then pairs[j]!.1 else if j == i then hole i else pairs[j]!.2
    let body := (tmpl.replaceFVars holes vals).abstract #[hole i]
    let M := mkLambda `x .default α body
    h := mkAppN (mkConst ``transport [1]) #[α, M, l, s, mkApp2 (mkConst ``Eq.refl [1]) α l, h]
  return h

end CFSG.KC.GridChunks

open Lean Elab Command Meta CFSG.KC.Tab CFSG.KC.GridChunks in
elab "#kc_grid_chunks " pre:ident blk:ident all:ident gg:num rr:num ch:ident
    "[" ts:ident,* "]" q:term:max : command => do
  let P := pre.getId
  let G := gg.getNat
  let R := rr.getNat
  let base := ch.getId
  let trees := ts.getElems.map (·.getId)
  let env ← getEnv
  let (Qc, pfs, tabs) ← liftTermElabM do
    let decls := trees.map fun t => (t, fun _ => pure fnT)
    withLocalDeclsD decls fun fvs => do
      let Q ← Term.elabTerm q (some (mkForall `q .default natT (mkSort .zero)))
      Term.synthesizeSyntheticMVarsNoPostponing
      let Q := normLits (← instantiateMVars Q)
      if Q.hasMVar then throwError "#kc_grid_chunks: the predicate has metavariables"
      let consts := trees.map fun t => mkConst (P ++ t)
      let close := fun (e : Expr) => e.replaceFVars fvs consts
      let Qc := close Q
      if Qc.hasFVar then throwError "#kc_grid_chunks: the predicate is not closed"
      let mut vals : Array (Array (Option Nat)) := trees.map fun _ => Array.replicate (G * R) none
      let mut chunks : Array (Name × Expr × Array (Expr × Expr)) := #[]
      for b in [0:G * R] do
        let t := base.appendAfter s!"{b}"
        let some ci := env.find? t | throwError "#kc_grid_chunks: unknown theorem {t}"
        let idx := idxE (lit (b / R)) R (lit (b % R))
        let (tmpl, pairs) := (diffE (mkApp Q idx).headBeta ci.type).run #[]
        for (s, l) in pairs do
          unless l matches .lit _ do
            throwError "#kc_grid_chunks: {t} differs from the predicate at a non-literal{indentExpr l}"
          if s.isApp && s.getAppNumArgs == 1 then
            if let some i := fvs.findIdx? (· == s.appFn!) then
              unless s.appArg! == idx do
                throwError "#kc_grid_chunks: {trees[i]!} is applied to a term other than the index"
              let some v := l.rawNatLit? | throwError "#kc_grid_chunks: {t}: not a Nat literal"
              vals := vals.modify i fun a => a.set! b (some v)
        chunks := chunks.push (t, tmpl, pairs.map fun (s, l) => (close s, l))
      let mut tabs : Array (Name × Array Nat) := #[]
      for i in [0:trees.size] do
        let mut vs : Array Nat := #[]
        for b in [0:G * R] do
          match vals[i]![b]! with
          | some v => vs := vs.push v
          | none => throwError "#kc_grid_chunks: {trees[i]!} has no value at {b}"
        tabs := tabs.push (P ++ trees[i]!, vs)
      let pfs := chunks.map fun (t, tmpl, pairs) => restate tmpl pairs (mkConst t)
      return (Qc, pfs, tabs)
  let ty := fun (x : Expr) => (mkApp Qc x).headBeta
  let blkS := blk.getId.toString
  liftCoreM <| withOptions (Elab.async.set · false) do
    for (F, vs) in tabs do
      addTable F vs
    for g in [0:G] do
      let lamR := mkLambda `r .default natT (ty (idxE (lit g) R (mkBVar 0)))
      let v := forallChain lamR R fun r => pfs[g * R + r]!
      let tyg := forallLt R fun r => ty (idxE (lit g) R r)
      CFSG.KC.addThmDecl <|
        { name := P ++ Name.mkSimple s!"{blkS}_{g}", levelParams := [], type := tyg, value := v }
    let lamG := mkLambda `g .default natT (forallLt R fun r => ty (idxE (mkBVar 2) R r))
    let vG := forallChain lamG G fun g => mkConst (P ++ Name.mkSimple s!"{blkS}_{g}")
    let tyG := forallLt G fun g => forallLt R fun r => ty (idxE (g.liftLooseBVars 0 2) R r)
    CFSG.KC.addThmDecl <| { name := P ++ all.getId, levelParams := [], type := tyG, value := vG }

end
