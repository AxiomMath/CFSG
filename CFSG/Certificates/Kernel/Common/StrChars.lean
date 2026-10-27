module

public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.Tab
public import Lean.Exception

open Lean Elab Command Meta

public section

namespace CFSG.KC.StrChars

open CFSG.KC.Tab

meta def litOf (t : Syntax) : TermElabM (Expr × String) := do
  let e ← instantiateMVars (← Term.elabTermEnsuringType t (mkConst ``String))
  match (← withTransparency .all <| whnf e) with
  | .lit (.strVal s) => pure (e, s)
  | r => throwError "#ks_chars_of: {e} reduces to {r}, not a string literal"

elab "#ks_chars_of " pre:ident t:term : command => do
  let P := pre.getId
  let (e, s) ← liftTermElabM (litOf t)
  let charE : Expr := mkConst ``Char
  let mk (ch : Char) : Expr := mkApp (mkConst ``Char.ofNat) (mkRawNatLit ch.toNat)
  let lst := s.toList.foldr (fun ch acc => mkApp3 (mkConst ``List.cons [0]) charE (mk ch) acc)
    (mkApp (mkConst ``List.nil [0]) charE)
  let lty := mkApp (mkConst ``List [0]) charE
  let strE := mkConst ``String
  withSync do
    addDef (P ++ `chars) lty lst
    let ty := mkApp3 (mkConst ``Eq [1]) strE e (mkApp (mkConst ``String.ofList) (mkConst (P ++ `chars)))
    let pf := mkApp2 (mkConst ``Eq.refl [1]) strE e
    let nEq := P ++ `eq
    CFSG.KC.addThmDecl <| { name := nEq, levelParams := [], type := ty, value := pf }

elab "#ks_codes_of " pre:ident t:term : command => do
  let P := pre.getId
  let (e, s) ← liftTermElabM (litOf t)
  let natE : Expr := mkConst ``Nat
  let lst := s.toList.foldr (fun ch acc => mkApp3 (mkConst ``List.cons [0]) natE
    (mkRawNatLit ch.toNat) acc) (mkApp (mkConst ``List.nil [0]) natE)
  let lty := mkApp (mkConst ``List [0]) natE
  let strE := mkConst ``String
  withSync do
    addDef (P ++ `codes) lty lst
    let mapped := mkApp4 (mkConst ``List.map [0, 0]) natE (mkConst ``Char) (mkConst ``Char.ofNat)
      (mkConst (P ++ `codes))
    let ty := mkApp3 (mkConst ``Eq [1]) strE e (mkApp (mkConst ``String.ofList) mapped)
    let pf := mkApp2 (mkConst ``Eq.refl [1]) strE e
    let nEq := P ++ `eq
    CFSG.KC.addThmDecl <| { name := nEq, levelParams := [], type := ty, value := pf }

end CFSG.KC.StrChars

end
