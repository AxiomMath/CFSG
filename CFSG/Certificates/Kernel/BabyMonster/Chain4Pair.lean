module

public import CFSG.Certificates.Kernel.BabyMonster.FourSound
public import CFSG.Certificates.Kernel.BabyMonster.PairSound
public meta import Lean

public section

namespace CFSG.KC.BM.Chain4Pair

open Lean Elab Tactic Meta

meta def natE : Expr := mkConst ``Nat
meta def listNatE : Expr := mkApp (mkConst ``List [0]) natE
meta def nilE (ty : Expr) : Expr := mkApp (mkConst ``List.nil [0]) ty
meta def consE (ty x xs : Expr) : Expr := mkApp3 (mkConst ``List.cons [0]) ty x xs

meta def lhsOf (tac : String) (nm : Name) : TacticM Expr := do
  let some ci := (← getEnv).find? nm | throwError "{tac}: unknown theorem {nm}"
  let some (_, b, _) := ci.type.eq? | throwError "{tac}: {nm} is not a check `b = true`"
  return b

meta def spreadRows (tac : String) (hs : Array Ident) : TacticM (Array (Name × Expr × Expr)) :=
  hs.mapM fun hR => do
    let nm ← realizeGlobalConstNoOverloadWithInfo hR
    let b ← lhsOf tac nm
    unless b.isAppOfArity ``CFSG.KC.BM.spreadOK 2 do
      throwError "{tac}: {nm} is not a check `spreadOK Rb Bs = true`"
    pure (nm, b.getArg! 0, b.getArg! 1)

meta def groupParts (tac : String) (rows : Array (Name × Expr × Expr)) (thm : Name) :
    TacticM (Expr × Expr × Array (Expr × Expr × Expr)) := do
  let b ← lhsOf tac thm
  let args := b.getAppArgs
  let (ws, f, pre, hr) ← if b.isAppOfArity ``CFSG.KC.BM.mulW4 6 then
      pure (args[0]!, "mulW4_sound", #[args[0]!], #[])
    else if b.isAppOfArity ``CFSG.KC.BM.mulR4 6 then
      let some (hn, Rb, Bs) := rows.find? (·.2.1 == args[0]!)
        | throwError "{tac}: no spread check `spreadOK {args[0]!} Bs = true` for {thm} in `using`"
      pure (consE listNatE Bs (nilE listNatE), "mulR4_sound", #[Rb, Bs], #[mkConst hn])
    else throwError "{tac}: {thm} is not a check `mulW4 Ws a₀ a₁ a₂ a₃ k = true` or `mulR4 …`"
  let k := args[5]!
  unless k.isAppOfArity ``CFSG.KC.BM.rhs4 5 do
    throwError "{tac}: {thm} does not end with `rhs4 Ds c₀ c₁ c₂ c₃`"
  let ds := k.getArg! 0
  let as := (Array.range 4).map fun i => args[1 + i]!
  let cs := (Array.range 4).map fun i => k.getArg! (1 + i)
  let lanes := (Array.range 4).map fun i =>
    (as[i]!, cs[i]!, mkAppN (mkConst (`CFSG.KC.BM.F4 ++ Name.mkSimple s!"{f}{i}"))
      (pre ++ #[ds] ++ as ++ cs ++ hr ++ #[mkConst thm]))
  return (ws, ds, lanes)

meta def strips (tac : String) (rows : Array (Name × Expr × Expr)) (F : Name) (n : Nat) :
    TacticM (Expr × Expr × Array (Expr × Expr × Expr)) := do
  let mut out : Array (Expr × Expr × Expr) := #[]
  let mut wd : Option (Expr × Expr) := none
  for g in [0:(n + 3) / 4] do
    let thm := F.appendAfter s!"_g{g}"
    let (ws, ds, lanes) ← groupParts tac rows thm
    match wd with
    | none => wd := some (ws, ds)
    | some (ws0, ds0) =>
      unless ws == ws0 && ds == ds0 do throwError "{tac}: {thm} has other words than {F}_g0"
    for i in [0:4] do
      if 4 * g + i < n then out := out.push lanes[i]!
  let some (ws, ds) := wd | throwError "{tac}: no strips"
  return (ws, ds, out)

syntax "bm_strips2_4 " ident num (" using " ident+)? : tactic

elab_rules : tactic
  | `(tactic| bm_strips2_4 $p:ident $n:num $[using $hRs*]?) => withMainContext do
    let tac := "bm_strips2_4"
    let n := n.getNat
    if n == 0 then throwError "{tac}: no strips"
    let rows ← spreadRows tac (hRs.getD #[])
    let (ws, ds, parts) ← strips tac rows p.getId n
    let mut acc := mkApp2 (mkConst ``CFSG.KC.BM.AllStrips2.nil) ws ds
    let mut as := nilE natE
    let mut cs := nilE natE
    for i' in [0:n] do
      let (a, c, pf) := parts[n - 1 - i']!
      acc := mkAppN (mkConst ``CFSG.KC.BM.AllStrips2.cons) #[ws, ds, a, c, as, cs, pf, acc]
      as := consE natE a as
      cs := consE natE c cs
    (← getMainGoal).assign acc
    replaceMainGoal []

syntax "bm_wchain4 " ident num ident (" using " ident+)? : tactic

elab_rules : tactic
  | `(tactic| bm_wchain4 $p:ident $n:num $w:ident $[using $hRs*]?) => withMainContext do
    let tac := "bm_wchain4"
    let P := p.getId
    let W := w.getId
    let rows ← spreadRows tac (hRs.getD #[])
    let fams := (Array.range n.getNat).map (fun i => P.appendAfter s!"_{i}") |>.push P
    let mut steps : Array (Expr × Expr × Name × Expr) := #[]
    for F in fams do
      let (ws, ds, parts) ← strips tac rows F 69
      unless ds.isAppOfArity ``List.nil 1 do throwError "{tac}: {F} has a right word {ds} ≠ []"
      let some nm := parts[0]!.2.1.constName? | throwError "{tac}: {F}_g0 has no constant target strip"
      let mut hs := mkApp (mkConst ``CFSG.KC.BM.AllStrips.nil) ws
      let mut as := nilE natE
      let mut cs := nilE natE
      for j' in [0:69] do
        let (a, c, pf) := parts[68 - j']!
        let c := mkApp2 (mkConst ``CFSG.KC.BM.mulW) ds c
        hs := mkAppN (mkConst ``CFSG.KC.BM.AllStrips.cons) #[ws, a, c, as, cs, pf, hs]
        as := consE natE a as
        cs := consE natE c cs
      steps := steps.push (ws, as, nm.getPrefix, hs)
    let lastC := mkConst steps.back!.2.2.1
    let mut acc := mkApp (mkConst ``CFSG.KC.BM.WChain.nil) lastC
    let mut Fs := nilE listNatE
    for k' in [0:steps.size] do
      let (ws, A, M, hs) := steps[steps.size - 1 - k']!
      let wfN := W.appendAfter M.getString!
      unless (← getEnv).contains wfN do throwError "{tac}: no well-formedness check {wfN}"
      let wfB := mkConst wfN
      acc := mkAppN (mkConst ``CFSG.KC.BM.WChain.step) #[ws, Fs, A, mkConst M, lastC, hs, wfB, acc]
      Fs ← mkAppM ``HAppend.hAppend #[ws, Fs]
    (← getMainGoal).assign acc
    replaceMainGoal []

end CFSG.KC.BM.Chain4Pair

end
