module

public meta import Lean
meta import all CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Harness

open Lean Elab Command

elab "#kc_listOf " pre:ident f:ident base:ident n:num : command => do
  let B := pre.getId ++ base.getId
  let lnE := CFSG.KC.Load.listNatE
  let ty := mkApp (mkConst ``List [0]) lnE
  let v := (List.range n.getNat).foldr
    (fun k acc => mkApp3 (mkConst ``List.cons [0]) lnE (mkConst (B.appendAfter s!"{k}")) acc)
    (mkApp (mkConst ``List.nil [0]) lnE)
  CFSG.KC.Load.withSync <| CFSG.KC.Load.addDef (pre.getId ++ f.getId) ty v true
