module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm
public import Lean.Exception

open Lean Elab Command

namespace CFSG.KC.BM.LoadRange

meta def natE : Expr := mkConst ``Nat
meta def listNatE : Expr := mkApp (mkConst ``List [0]) natE

meta def mkList (ty : Expr) (es : Array Expr) : Expr :=
  es.foldr (fun e acc => mkApp3 (mkConst ``List.cons [0]) ty e acc) (mkApp (mkConst ``List.nil [0]) ty)

meta def rel (P : Name) (n : Name) : Name :=
  let r := n.getRoot
  if r == `CFSG || r == `Nat || r == `Bool || r == `List then n else P ++ n

end CFSG.KC.BM.LoadRange

open CFSG.KC.BM.LoadRange

declare_syntax_cat bmrterm
syntax num : bmrterm
syntax ident : bmrterm
syntax "(" ident bmrterm* ")" : bmrterm
syntax "[" bmrterm* "]" : bmrterm

meta partial def CFSG.KC.BM.LoadRange.term (P : Name) : TSyntax `bmrterm → Except String Expr
  | `(bmrterm| $n:num) => .ok (mkRawNatLit n.getNat)
  | `(bmrterm| $i:ident) =>
    if i.getId == `true then .ok (mkConst ``Bool.true)
    else if i.getId == `false then .ok (mkConst ``Bool.false)
    else .ok (mkConst (rel P i.getId))
  | `(bmrterm| ($f:ident $args*)) => do
    if f.getId == `L2 then return mkList listNatE (← args.mapM (term P))
    .ok (mkAppN (mkConst (rel P f.getId)) (← args.mapM (term P)))
  | `(bmrterm| [$args*]) => do .ok (mkList natE (← args.mapM (term P)))
  | _ => .error "bad term"

elab "#bm_range " pre:ident tag:ident lo:num hi:num t:bmrterm : command => do
  let P := pre.getId
  match CFSG.KC.BM.LoadRange.term P t with
  | .error e => throwError e
  | .ok e => liftCoreM <| withOptions (Elab.async.set · false) do
    for k in [lo.getNat:hi.getNat] do
      let name := P ++ tag.getId.appendAfter s!"{k}"
      let b := mkApp e (mkRawNatLit k)
      let t0 ← IO.monoNanosNow
      CFSG.KC.addThmDecl <|
        { name, levelParams := [], type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) b (mkConst ``Bool.true),
          value := reflBoolTrue }
      let ms := ((← IO.monoNanosNow) - t0).toFloat / 1e6
      logInfo m!"BMTIME {name.componentsRev.head!} {ms} ms"
