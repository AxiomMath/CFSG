module

public import CFSG.Certificates.Kernel.BabyMonster.FourSound
public meta import Lean
public import CFSG.Certificates.Kernel.BSeed.Sound

public section

namespace CFSG.KC.BM.Chain4

open Lean Elab Tactic Meta

meta def natE : Expr := mkConst ``Nat
meta def listNatE : Expr := mkApp (mkConst ``List [0]) natE

meta def lhsOf (nm : Name) : TacticM Expr := do
  let some ci := (← getEnv).find? nm | throwError "unknown theorem {nm}"
  let some (_, b, _) := ci.type.eq? | throwError "{nm} is not a check `b = true`"
  return b

syntax "bm_strips4 " ident num (" using " ident)? : tactic

elab_rules : tactic
  | `(tactic| bm_strips4 $p:ident $n:num $[using $hR?]?) => withMainContext do
    let P := p.getId
    let n := n.getNat
    if n == 0 then throwError "bm_strips4: no strips"
    let rows ← hR?.mapM fun hR => do
      let nm ← realizeGlobalConstNoOverloadWithInfo hR
      let b ← lhsOf nm
      unless b.isAppOfArity ``CFSG.KC.BM.spreadOK 2 do
        throwError "bm_strips4: {nm} is not a check `spreadOK Rb Bs = true`"
      pure (nm, b.getArg! 0, b.getArg! 1)
    let mut parts : Array (Expr × Expr × Expr × Expr) := #[]
    for g in [0:(n + 3) / 4] do
      let thm := P.appendAfter s!"_g{g}"
      let b ← lhsOf thm
      let args := b.getAppArgs
      let (ws, f, pre) ← match rows with
        | none =>
          unless b.isAppOfArity ``CFSG.KC.BM.mulW4 6 do
            throwError "bm_strips4: {thm} is not a check `mulW4 Ws a₀ a₁ a₂ a₃ k = true`"
          pure (args[0]!, "mulW4_sound", #[args[0]!])
        | some (hn, Rb, Bs) =>
          unless b.isAppOfArity ``CFSG.KC.BM.mulR4 6 do
            throwError "bm_strips4: {thm} is not a check `mulR4 Rb a₀ a₁ a₂ a₃ k = true`"
          unless args[0]! == Rb do throwError "bm_strips4: {thm} uses other rows than {hn}"
          pure (mkApp3 (mkConst ``List.cons [0]) listNatE Bs (mkApp (mkConst ``List.nil [0]) listNatE),
            "mulR4_sound", #[Rb, Bs])
      let k := args[5]!
      unless k.isAppOfArity ``CFSG.KC.BM.rhs4 5 do
        throwError "bm_strips4: {thm} does not end with `rhs4 Ds c₀ c₁ c₂ c₃`"
      let ds := k.getArg! 0
      let as := (Array.range 4).map fun i => args[1 + i]!
      let cs := (Array.range 4).map fun i => k.getArg! (1 + i)
      for i in [0:4] do
        if 4 * g + i < n then
          let hr := match rows with | none => #[] | some (hn, _, _) => #[mkConst hn]
          let pf := mkAppN (mkConst (`CFSG.KC.BM.F4 ++ Name.mkSimple s!"{f}{i}"))
            (pre ++ #[ds] ++ as ++ cs ++ hr ++ #[mkConst thm])
          parts := parts.push (ws, as[i]!, mkApp2 (mkConst ``CFSG.KC.BM.mulW) ds cs[i]!, pf)
    let ws := parts[0]!.1
    let mut acc := mkApp (mkConst ``CFSG.KC.BM.AllStrips.nil) ws
    let mut as := mkApp (mkConst ``List.nil [0]) natE
    let mut cs := mkApp (mkConst ``List.nil [0]) natE
    for i' in [0:n] do
      let (_, a, c, pf) := parts[n - 1 - i']!
      acc := mkAppN (mkConst ``CFSG.KC.BM.AllStrips.cons) #[ws, a, c, as, cs, pf, acc]
      as := mkApp3 (mkConst ``List.cons [0]) natE a as
      cs := mkApp3 (mkConst ``List.cons [0]) natE c cs
    (← getMainGoal).assign acc
    replaceMainGoal []

end CFSG.KC.BM.Chain4

end
