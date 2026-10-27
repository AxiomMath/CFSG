module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Common.Tab

open Lean Elab Command

open CFSG.KC.Tab in
elab "#kc_tab_cat " f:ident g:ident n:num s:num : command => do
  let F := f.getId
  let G := g.getId
  let n := n.getNat
  let s := s.getNat
  let size := 1 <<< Nat.log2 (2 * (max n 1) - 1)
  let leaf (j : Nat) : Expr :=
    if j < n then
      mkLambda `i .default natT (mkApp (mkConst (G.appendAfter s!"{j}"))
        (mkApp2 (mkConst ``Nat.land) (mkBVar 0) (lit ((1 <<< s) - 1))))
    else constFn (lit 0)
  withSync <| addDef F fnT (table leaf size s)
