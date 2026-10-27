module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.DataRoot

open Lean Elab Command

public section

namespace CFSG.KC.Tab

meta def natT (_ : Unit := ()) : Expr := mkConst ``Nat
meta def fnT (_ : Unit := ()) : Expr := mkForall `i .default natT natT
meta def lit (n : Nat) : Expr := mkRawNatLit n

meta def node (l r : Expr) (t : Nat) : Expr :=
  let motive := mkLambda `_ .default (mkConst ``Bool) fnT
  let i := mkBVar 0
  mkLambda `i .default natT
    (mkAppN (mkConst ``Bool.rec [Level.one]) #[motive, l, r, mkApp2 (mkConst ``Nat.ble) (lit t) i, i])

meta partial def tree (leaf : Nat → Expr) (lo size base : Nat) : Expr :=
  if size == 1 then leaf lo
  else
    let h := size / 2
    node (tree leaf lo h base) (tree leaf (lo + h) h base) ((lo + h) <<< base)

meta def table (leaf : Nat → Expr) (size base : Nat) : Expr :=
  if size == 1 then leaf 0
  else
    mkLambda `i .default natT (mkApp (tree leaf 0 size base)
      (mkApp2 (mkConst ``Nat.land) (mkBVar 0) (lit ((size <<< base) - 1))))

meta def constFn (e : Expr) : Expr := mkLambda `i .default natT e

meta partial def natLE (b : ByteArray) (lo hi : Nat) : Nat :=
  if hi ≤ lo + 8 then
    Id.run do
      let mut acc := 0
      for k in [0:hi - lo] do
        acc := acc + (b[lo + k]!.toNat <<< (8 * k))
      return acc
  else
    let mid := lo + (hi - lo) / 2
    natLE b lo mid + (natLE b mid hi <<< (8 * (mid - lo)))

meta def addDef (name : Name) (type value : Expr) : CoreM Unit :=
  addDecl (forceExpose := true) <| .defnDecl
    { name, levelParams := [], type, value, hints := .regular 0, safety := .safe }

meta def withSync (x : CoreM Unit) : CommandElabM Unit :=
  liftCoreM <| withOptions (Elab.async.set · false) x

meta def readPinned {m : Type → Type} [Monad m] [MonadOptions m] [MonadLiftT IO m]
    (rel : String) (size hash : Nat) : m ByteArray := do
  let path := (← CFSG.KC.dataRoot) / rel
  monadLift (m := IO) do
  let b ← IO.FS.readBinFile path
  unless b.size == size && b.hash.toNat == hash do
    throw (IO.userError
      s!"data file {path}: size {b.size} hash {b.hash.toNat}, pinned size {size} hash {hash}")
  return b

end CFSG.KC.Tab

open CFSG.KC.Tab in
elab "#kc_ktreeT " pre:ident id:ident path:str lb:num size:num hash:num : command => do
  let b ← readPinned path.getString size.getNat hash.getNat
  let F := pre.getId ++ id.getId
  let leafBytes := lb.getNat
  let nLeaves := (b.size + leafBytes - 1) / leafBytes
  let h := Nat.log2 (2 * nLeaves - 1)
  let leafName := fun k => if k < nLeaves then F ++ Name.mkSimple s!"L{k}" else F ++ `Z
  withSync do
    addDef (F ++ `Z) natT (lit 0)
    for k in [0:nLeaves] do
      let s := k * leafBytes
      addDef (leafName k) natT (lit (natLE b s (min b.size (s + leafBytes))))
    addDef F fnT (table (fun k => constFn (mkConst (leafName k))) (1 <<< h) 0)

open CFSG.KC.Tab in
elab "#kc_selectT " pre:ident id:ident base:ident n:num : command => do
  let n := n.getNat
  let d := max 1 (Nat.log2 (2 * n - 1))
  let F := pre.getId ++ id.getId
  let B := pre.getId ++ base.getId
  let leaf := fun k => constFn (if k < n then mkConst (B.appendAfter s!"{k}") else lit 0)
  withSync <| addDef F fnT (table leaf (1 <<< d) 0)

end
