module

public import CFSG.Certificates.Kernel.Common.Harness
meta import all CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Certificates.Kernel.Common.Benes
meta import all CFSG.Certificates.Kernel.Common.Benes

open Lean Elab Command Term

elab "#kc_natval " id:ident " := " t:term : command => do
  let name := (← getCurrNamespace) ++ id.getId
  let v ← liftTermElabM do
    let e ← elabTerm t (some (mkConst ``Nat))
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    if e.hasMVar || e.hasFVar then throwError "#kc_natval: the term is not closed"
    CFSG.KC.Benes.kNat (toString id.getId) e
  liftCoreM <| CFSG.KC.Load.addDef name (mkConst ``Nat) (mkRawNatLit v) true
