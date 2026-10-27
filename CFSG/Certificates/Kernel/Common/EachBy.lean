module

public meta import Lean

open Lean Elab Command

elab "#kc_each_by " f:ident lo:num hi:num l:ident : command => do
  for k in [lo.getNat:hi.getNat] do
    let nm := mkIdent (f.getId.appendAfter s!"{k}")
    let kq := Syntax.mkNumLit (toString k)
    elabCommand (← `(theorem $nm : $f $kq = true := $l $kq (by decide)))
