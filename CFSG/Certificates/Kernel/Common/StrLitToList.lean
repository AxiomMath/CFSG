module

public meta import Lean
public import Lean.Expr

public section

namespace CFSG.KC.StrLitToList

open Lean Meta Simp

simproc strLitToList (String.toList _) := fun e => do
  let_expr String.toList s := e | return .continue
  let .lit (.strVal str) := s.consumeMData | return .continue
  let charE := mkConst ``Char
  let strE := mkConst ``String
  let l := str.toList.foldr
    (fun c acc => mkApp3 (mkConst ``List.cons [0]) charE
      (mkApp (mkConst ``Char.ofNat) (mkRawNatLit c.toNat)) acc)
    (mkApp (mkConst ``List.nil [0]) charE)
  let lty := mkApp (mkConst ``List [0]) charE
  let ofL := mkApp (mkConst ``String.ofList) l
  let toL := mkConst ``String.toList
  let pf1 := mkApp6 (mkConst ``congrArg [1, 1]) strE lty s ofL toL
    (mkApp2 (mkConst ``Eq.refl [1]) strE s)
  let pf2 := mkApp (mkConst ``String.toList_ofList) l
  let pf := mkApp6 (mkConst ``Eq.trans [1]) lty (mkApp toL s) (mkApp toL ofL) l pf1 pf2
  return .done { expr := l, proof? := some pf }

end CFSG.KC.StrLitToList
