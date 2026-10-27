module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm
public import Lean.Message

open Lean Elab Command

namespace CFSG.KC.BM.LoadFour

meta def N : Nat := 4370

meta def natE : Expr := mkConst ``Nat
meta def listNatE : Expr := mkApp (mkConst ``List [0]) natE

meta def mkList (ty : Expr) (es : Array Expr) : Expr :=
  es.foldr (fun e acc => mkApp3 (mkConst ``List.cons [0]) ty e acc) (mkApp (mkConst ``List.nil [0]) ty)

meta def rel (P : Name) (n : Name) : Name :=
  let r := n.getRoot
  if r == `CFSG || r == `Nat || r == `Bool || r == `List then n else P ++ n

meta def stripE (P M : Name) (j : Nat) : Expr :=
  if (N + 63) / 64 ≤ j then mkRawNatLit 0
  else if M == `I then mkApp (mkConst `CFSG.KC.BM.idS) (mkRawNatLit j)
  else mkConst (rel P M ++ Name.mkSimple s!"s{j}")

meta def wordE (P : Name) (ws : Array Name) : Expr :=
  mkList listNatE (ws.map fun w => mkConst (rel P w))

meta def addGroups (P tag : Name) (lhs : Expr) (a c : Name) (ds : Expr) : CommandElabM Unit :=
  liftCoreM <| withOptions (Elab.async.set · false) do
    let mut tot := 0.0
    for g in [0:((N + 63) / 64 + 3) / 4] do
      let j := 4 * g
      let k := mkAppN (mkConst `CFSG.KC.BM.rhs4)
        #[ds, stripE P c j, stripE P c (j + 1), stripE P c (j + 2), stripE P c (j + 3)]
      let b := mkAppN lhs
        #[stripE P a j, stripE P a (j + 1), stripE P a (j + 2), stripE P a (j + 3), k]
      let t0 ← IO.monoNanosNow
      CFSG.KC.addThmDecl <|
        { name := P ++ tag.appendAfter s!"_g{g}", levelParams := [],
          type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) b (mkConst ``Bool.true),
          value := reflBoolTrue }
      tot := tot + ((← IO.monoNanosNow) - t0).toFloat / 1e6
    logInfo m!"BMTIME {tag} {tot} ms"

end CFSG.KC.BM.LoadFour

open CFSG.KC.BM.LoadFour

elab "#bm_mul4 " pre:ident tag:ident a:ident "[" bs:ident* "]" c:ident "[" ds:ident* "]" : command => do
  let P := pre.getId
  addGroups P tag.getId (mkApp (mkConst `CFSG.KC.BM.mulW4) (wordE P (bs.map (·.getId))))
    a.getId c.getId (wordE P (ds.map (·.getId)))

elab "#bm_mulr4 " pre:ident tag:ident a:ident r:ident c:ident "[" ds:ident* "]" : command => do
  let P := pre.getId
  addGroups P tag.getId (mkApp (mkConst `CFSG.KC.BM.mulR4) (mkConst (rel P r.getId)))
    a.getId c.getId (wordE P (ds.map (·.getId)))
