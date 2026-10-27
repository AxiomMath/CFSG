module

public meta import Lean
public import CFSG.Certificates.Kernel.Common.Harness

open Lean Elab Command

elab "#kc_slice_range " fId:ident pre:ident lo:num hi:num : command => do
  for i in [lo.getNat:hi.getNat] do
    let nm := mkIdent (pre.getId.appendAfter s!"{i}")
    let lit := Syntax.mkNumLit (toString i)
    elabCommand (← `(command| theorem $nm : $fId (nat_lit $lit) = true := by quickRfl))
