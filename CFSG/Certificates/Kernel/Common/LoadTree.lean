module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Common.Tab

open Lean Elab Command CFSG.KC.Tab

namespace CFSG.KC.LoadTree

meta partial def bitDispatch (leafs : Array Expr) (p k : Nat) (off : Nat) : Expr :=
  if k == 0 then leafs[off]!
  else
    let bit := mkApp2 (mkConst ``Nat.beq)
      (mkApp2 (mkConst ``Nat.land) (.bvar 0) (mkRawNatLit (1 <<< (p - 1)))) (mkRawNatLit 0)
    let lo := bitDispatch leafs (p - 1) (k - 1) off
    let hi := bitDispatch leafs (p - 1) (k - 1) (off + (1 <<< (k - 1)))
    mkApp4 (mkConst ``cond [1]) natT bit lo hi

meta def addDefC (name : Name) (type value : Expr) : CoreM Unit := do
  addDef name type value
  compileDecls #[name]

meta partial def addNodes (leafName : Nat → Name) (name : Name) (lo h fan : Nat) : CoreM Unit := do
  let k := min fan h
  let children ← if k == h then
      pure <| (Array.range (1 <<< k)).map fun c => mkConst (leafName (lo + c))
    else
      (Array.range (1 <<< k)).mapM fun c => do
        let cn := name ++ Name.mkSimple s!"c{c}"
        addNodes leafName cn (lo + (c <<< (h - k))) (h - k) fan
        pure (mkApp (mkConst cn) (.bvar 0))
  addDefC name fnT (mkLambda `b .default natT (bitDispatch children h k 0))

end CFSG.KC.LoadTree

open CFSG.KC.LoadTree in
elab "#load_ktree " id:ident path:str lb:num fan:num : command => do
  let b ← IO.FS.readBinFile path.getString
  let F := id.getId
  let leafBytes := lb.getNat
  let nLeaves := (b.size + leafBytes - 1) / leafBytes
  let h := Nat.log2 (2 * nLeaves - 1)
  let leafName := fun k => if k < nLeaves then F ++ Name.mkSimple s!"L{k}" else F ++ `Z
  withSync do
    addDefC (F ++ `Z) natT (lit 0)
    for k in [0:nLeaves] do
      let s := k * leafBytes
      addDefC (leafName k) natT (lit (natLE b s (min b.size (s + leafBytes))))
    addNodes leafName F 0 h fan.getNat
