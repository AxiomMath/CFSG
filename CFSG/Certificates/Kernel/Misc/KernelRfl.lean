module

public meta import Lean
public import Lean.Exception

public section

open Lean Elab Tactic Meta in
elab "kernelRfl" : tactic => liftMetaFinishingTactic fun g => do
  let t ← whnfR (← g.getType)
  let some (_, a, _) := t.eq? | throwError "kernelRfl: the goal is not an equality"
  g.assign (← mkEqRefl a)

end
