module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Common.Tab

open Lean Elab Command

public section

namespace CFSG.KC.IntWords

meta def intLit : Int → Expr
  | .ofNat n => mkApp (mkConst ``Int.ofNat) (mkRawNatLit n)
  | .negSucc n => mkApp (mkConst ``Int.negSucc) (mkRawNatLit n)

meta def listLit (ty : Expr) (l : List Expr) : Expr :=
  l.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) ty x acc)
    (mkApp (mkConst ``List.nil [0]) ty)

end CFSG.KC.IntWords

open CFSG.KC.IntWords in
elab "#kc_intwords_list " pre:ident sId:ident : command => do
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let l ← liftTermElabM <| unsafe evalConst (List (List Int)) sN
  let intT := mkConst ``Int
  let wT := mkApp (mkConst ``List [0]) intT
  let e := listLit wT (l.map fun w => listLit intT (w.map intLit))
  CFSG.KC.Tab.withSync <| CFSG.KC.Tab.addDef pre.getId (mkApp (mkConst ``List [0]) wT) e

end
