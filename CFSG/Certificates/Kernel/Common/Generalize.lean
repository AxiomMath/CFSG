module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm
public import Lean.Meta.Basic

namespace CFSG.KC.Generalize

open Lean Meta Elab Command Term

meta structure St where
  base : NameSet
  keys : Array (Expr × Expr)
  lctx : LocalContext
  taint : Std.HashMap Name Bool := {}
  cache : Std.HashMap Expr Expr := {}
  hyps : Array (FVarId × Name × List Level × Expr) := #[]

abbrev GM := StateRefT St MetaM

meta def inPkg (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | none => true
  | some i =>
    let r := (env.header.moduleNames[i.toNat]!).getRoot
    r == `CFSG || r == `Certificates || r == `CertificateChecks || r == `TauCeti

meta def repo (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | none => true
  | some i =>
    let r := (env.header.moduleNames[i.toNat]!).getRoot
    r == `CFSG || r == `Certificates || r == `CertificateChecks

meta partial def tainted (c : Name) : GM Bool := do
  let s ← get
  if s.base.contains c then return true
  if let some b := s.taint[c]? then return b
  let env ← getEnv
  if !inPkg env c then return false
  modify fun s => { s with taint := s.taint.insert c false }
  let some ci := env.find? c | return false
  let mut cs := ci.type.getUsedConstants
  match ci with
  | .defnInfo d => cs := cs ++ d.value.getUsedConstants
  | .opaqueInfo d => cs := cs ++ d.value.getUsedConstants
  | .inductInfo d => for k in d.ctors do cs := cs.push k
  | .axiomInfo _ =>
    if repo env c then
      unless ← isProp ci.type do
        throwError "{c} is a definition whose body this module does not see: `import all` its module"
  | _ => pure ()
  let mut t := false
  for k in cs do
    if ← tainted k then
      t := true
      break
  modify fun s => { s with taint := s.taint.insert c t }
  return t

meta def propStruct? (c : Name) : MetaM (Option InductiveVal) := do
  let env ← getEnv
  let some (.inductInfo d) := env.find? c | return none
  unless d.ctors.length == 1 && isStructure env c do return none
  let r ← forallTelescope d.type fun _ b => pure b
  return if r.isProp then some d else none

meta def numFields (d : InductiveVal) : MetaM Nat := do
  let some (.ctorInfo k) := (← getEnv).find? d.ctors.head! | throwError "no constructor of {d.name}"
  return k.numFields

meta def fieldTypes (d : InductiveVal) (us : List Level) (ps : Array Expr) :
    MetaM (Array Expr) := do
  let k ← getConstInfo d.ctors.head!
  let mut t ← instantiateForall (k.instantiateTypeLevelParams us) ps
  let mut fs := #[]
  while t.isForall do
    let .forallE _ a b _ := t | unreachable!
    if b.hasLooseBVars then throwError "dependent field in {d.name}"
    fs := fs.push a
    t := b
  return fs

meta def mkAnd (fs : Array Expr) : Expr :=
  if fs.isEmpty then mkConst ``True
  else fs.pop.foldr (fun a b => mkApp2 (mkConst ``And) a b) fs.back!

meta def structOf (a : Expr) : GM (Option (InductiveVal × List Level × Array Expr)) := do
  let .const c us := a.getAppFn | return none
  if !(← tainted c) then return none
  let some d ← propStruct? c | return none
  return some (d, us, a.getAppArgs)

mutual

meta partial def tr (e : Expr) : GM Expr := do
  for (k, v) in (← get).keys do
    if e == k then return v
  if let some r := (← get).cache[e]? then return r
  let r ← trCore e
  modify fun s => { s with cache := s.cache.insert e r }
  return r

meta partial def trCore (e : Expr) : GM Expr := do
  match e with
  | .const c us => trConst c us
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    if let .const c us := f then
      if ← tainted c then
        let env ← getEnv
        if let some d ← propStruct? c then
          unless args.size == d.numParams do
            throwError "the structure {c} is applied to {args.size} arguments"
          return mkAnd (← (← fieldTypes d us args).mapM tr)
        if let some (.ctorInfo k) := env.find? c then
          if (← propStruct? k.induct).isSome && k.numFields == 1 &&
              args.size == k.numParams + 1 then
            return ← tr args.back!
          throwError "the constructor {c} of a tainted structure"
        if let some p := env.getProjectionFnInfo? c then
          let s := p.ctorName.getPrefix
          if let some d ← propStruct? s then
            if (← numFields d) == 1 && args.size == p.numParams + 1 then
              return ← tr args.back!
            throwError "the projection {c} of a structure with several fields"
        if let some ci@(.defnInfo _) := env.find? c then
          return ← tr ((ci.instantiateValueLevelParams! us).beta args)
    let f' ← tr f
    let args' ← args.mapM tr
    return (mkAppN f' args').headBeta
  | .lam n t b bi =>
    let bi' := if bi.isInstImplicit && (← structOf t).isSome then .default else bi
    return .lam n (← tr t) (← tr b) bi'
  | .forallE n t b bi =>
    let bi' := if bi.isInstImplicit && (← structOf t).isSome then .default else bi
    return .forallE n (← tr t) (← tr b) bi'
  | .letE n t v b nd => return .letE n (← tr t) (← tr v) (← tr b) nd
  | .mdata m b => return .mdata m (← tr b)
  | .proj s i b =>
    if ← tainted s then
      if let some d ← propStruct? s then
        if i == 0 && (← numFields d) == 1 then return ← tr b
        throwError "the projection {i} of {s}"
    return .proj s i (← tr b)
  | _ => return e

meta partial def trConst (c : Name) (us : List Level) : GM Expr := do
  if (← get).base.contains c then throwError "the input constant {c} is not a key here"
  if !(← tainted c) then return .const c us
  let ci ← getConstInfo c
  if let some d ← propStruct? c then
    if d.numParams == 0 then return mkAnd (← (← fieldTypes d us #[]).mapM tr)
  match ci with
  | .defnInfo _ => tr (ci.instantiateValueLevelParams! us)
  | .thmInfo _ | .axiomInfo _ =>
    unless ← isProp (ci.instantiateTypeLevelParams us) do
      throwError "the constant {c} is tainted data without a visible definition"
    for (fv, n, ls, _) in (← get).hyps do
      if n == c && ls == us then return .fvar fv
    let ty ← tr (ci.instantiateTypeLevelParams us)
    let fv ← mkFreshFVarId
    modify fun s => { s with
      hyps := s.hyps.push (fv, c, us, ty)
      lctx := s.lctx.mkLocalDecl fv c ty }
    return .fvar fv
  | _ => throwError "cannot generalize the constant {c}"

end

meta partial def adaptTo (T t : Expr) : GM Expr := do
  let T := T.headBeta
  match T with
  | .forallE n a b bi =>
    withLocalDecl n bi a fun x => do
      let arg ← match ← structOf a with
        | some (d, _, _) =>
          unless (← numFields d) == 1 do throwError "a binder of a structure with several fields"
          pure (Expr.proj d.name 0 x)
        | none => pure x
      mkLambdaFVars #[x] (← adaptTo (b.instantiate1 x) (mkApp t arg))
  | _ =>
    match ← structOf T with
    | some (d, us, ps) =>
      let fs ← fieldTypes d us ps
      let mut parts := #[]
      let mut rest := t
      for i in [0:fs.size] do
        if i + 1 == fs.size then
          parts := parts.push rest
        else
          let r := mkAnd (fs.extract (i + 1) fs.size)
          parts := parts.push (mkApp3 (mkConst ``And.left) fs[i]! r rest)
          rest := mkApp3 (mkConst ``And.right) fs[i]! r rest
      let mut parts' := #[]
      for i in [0:fs.size] do
        parts' := parts'.push (← adaptTo fs[i]! parts[i]!)
      return mkAppN (mkConst d.ctors.head! us) (ps ++ parts')
    | none =>
      if T.isAppOfArity ``And 2 then
        let tt ← whnf (← inferType t)
        unless tt.isAppOfArity ``And 2 do throwError "expected a conjunction: {tt}"
        let a' := tt.appFn!.appArg!
        let b' := tt.appArg!
        let l ← adaptTo T.appFn!.appArg! (mkApp3 (mkConst ``And.left) a' b' t)
        let r ← adaptTo T.appArg! (mkApp3 (mkConst ``And.right) a' b' t)
        return mkApp4 (mkConst ``And.intro) T.appFn!.appArg! T.appArg! l r
      let .const c _ := T.getAppFn | return t
      if !(← tainted c) then return t
      let some (.defnInfo _) := (← getEnv).find? c | return t
      let some T' ← unfoldDefinition? T | return t
      adaptTo T' t

meta partial def adaptFrom (T e : Expr) : GM Expr := do
  match T with
  | .forallE n a b bi =>
    match ← structOf a with
    | some (d, us, ps) =>
      unless (← numFields d) == 1 do throwError "a binder of a structure with several fields"
      let fs ← fieldTypes d us ps
      withLocalDecl n .default fs[0]! fun x => do
        let s := mkAppN (mkConst d.ctors.head! us) (ps.push x)
        mkLambdaFVars #[x] (← adaptFrom (b.instantiate1 s) (mkApp e s))
    | none =>
      withLocalDecl n bi a fun x => do
        mkLambdaFVars #[x] (← adaptFrom (b.instantiate1 x) (mkApp e x))
  | _ =>
    match ← structOf T with
    | some (d, _, _) =>
      unless (← numFields d) == 1 do throwError "a structure with several fields"
      return Expr.proj d.name 0 e
    | none => return e

syntax (name := kcGeneralize) "#kc_generalize " ident bracketedBinder* " using " "["
  (term " ↦ " term),* "]" (" from " "[" ident,* "]")? " : " term : command

elab_rules : command
  | `(#kc_generalize $g:ident $bs* using [$[$ka ↦ $kb],*] $[from [$fs,*]]? : $s) => do
    let name := (← getCurrNamespace) ++ g.getId
    liftTermElabM <| withOptions (Elab.async.set · false) do
      elabBinders bs fun xs => do
        let mut keys := #[]
        for (a, b) in ka.zip kb do
          keys := keys.push (← elabTerm a none, ← elabTerm b none)
        let S ← elabType s
        synthesizeSyntheticMVarsNoPostponing
        let S ← instantiateMVars S
        keys ← keys.mapM fun (a, b) => return (← instantiateMVars a, ← instantiateMVars b)
        let mut base : NameSet := {}
        for (a, _) in keys do
          if let .const c _ := a then base := base.insert c
        if let some fs := fs then
          for f in fs.getElems do
            base := base.insert (← realizeGlobalConstNoOverloadWithInfo f)
        let (body, st) ← (tr S).run { base, keys, lctx := ← getLCtx }
        let stmt ← withLCtx st.lctx (← getLocalInstances) do
          mkForallFVars (st.hyps.map fun h => .fvar h.1) body
        if let some c := stmt.find? fun x => x.isConst && base.contains x.constName! then
          throwError "the statement still mentions the input {c}"
        let value ← instantiateMVars (← mkLambdaFVars xs stmt)
        if value.hasMVar || value.hasFVar then throwError "the statement is not closed"
        let type ← instantiateMVars (← mkForallFVars xs (mkSort 0))
        if type.hasMVar || type.hasLevelMVar then throwError "the binder types are not determined"
        try
          addDecl (forceExpose := true) <| .defnDecl
            { name, levelParams := [], type, value, hints := ReducibilityHints.abbrev,
              safety := .safe }
        catch ex => throwError "the definition {name}: {ex.toMessageData}"
        let args ← xs.mapM fun x => do
          match keys.find? (·.2 == x) with
          | some (a, _) => pure a
          | none => throwError "no key is mapped to the variable {x}"
        let gA := mkAppN (mkConst name) args
        let (pf, _) ← (withLocalDeclD `h gA fun h => do
            let mut hargs := #[]
            for (_, c, us, _) in st.hyps do
              let ci ← getConstInfo c
              hargs := hargs.push (← adaptFrom (ci.instantiateTypeLevelParams us) (.const c us))
            mkLambdaFVars #[h] (← adaptTo S (mkAppN h hargs))).run st
        let instTy ← mkArrow gA S
        let pf ← instantiateMVars pf
        try
          CFSG.KC.addThmDecl <| { name := name ++ `inst, levelParams := [], type := instTy, value := pf }
        catch ex => throwError "the theorem {name ++ `inst}: {ex.toMessageData}"
        logInfo m!"{name}: {st.hyps.size} hypotheses {st.hyps.map (·.2.1)}"

end CFSG.KC.Generalize
