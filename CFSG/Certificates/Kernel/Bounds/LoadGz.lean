module

public meta import Lean
public import CFSG.Certificates.Kernel.Bounds.Load
public import CFSG.Certificates.Kernel.Common.HarnessGz
meta import CFSG.Certificates.Kernel.Bounds.Load
meta import CFSG.Certificates.Kernel.Common.Tab
meta import all CFSG.Certificates.Kernel.Common.Harness
meta import all CFSG.Certificates.Kernel.Common.HarnessGz

open Lean Elab Command

open CFSG.Certificates.KB.Load CFSG.KC.Gz in
elab "#kc_blocked_gz " nm:ident path:str logRecs:num logStride:num mask:num size:num hash:num :
    command => do
  let b ← readPinnedGz path.getString size.getNat hash.getNat
  let F := nm.getId
  let lr := logRecs.getNat
  let ls := logStride.getNat
  let leafBytes := (1 <<< (lr + ls)) / 8
  let nLeaves := (b.size + leafBytes - 1) / leafBytes
  withSync do
    for j in [0:nLeaves] do
      let lo := j * leafBytes
      let hi := min b.size (lo + leafBytes)
      addDef (F ++ Name.mkSimple s!"b{j}") natT (lit (natLE b lo hi))
    let leaf (j : Nat) : Expr :=
      let blk := if j < nLeaves then mkConst (F ++ Name.mkSimple s!"b{j}") else lit 0
      let i := mkBVar 0
      let off := mkApp2 (mkConst ``Nat.shiftLeft)
        (mkApp2 (mkConst ``Nat.land) i (lit ((1 <<< lr) - 1))) (lit ls)
      mkLambda `i .default natT
        (mkApp2 (mkConst ``Nat.land) (mkApp2 (mkConst ``Nat.shiftRight) blk off) (lit mask.getNat))
    addDef F fnT (CFSG.KC.Tab.table leaf (nextPow2 (max nLeaves 1)) lr)

open CFSG.Certificates.KB.Load CFSG.KC.Gz in
elab "#kc_items_gz " nm:ident path:str size:num hash:num : command => do
  let b ← readPinnedGz path.getString size.getNat hash.getNat
  let F := nm.getId
  let its := items b
  withSync do
    for j in [0:its.size] do
      let (lo, hi) := its[j]!
      addDef (F ++ Name.mkSimple s!"b{j}") natT (lit (natLE b lo hi))
    let leaf (j : Nat) : Expr :=
      mkApp (mkConst `CFSG.Certificates.KB.constN)
        (if j < its.size then mkConst (F ++ Name.mkSimple s!"b{j}") else lit 0)
    addDef F fnT (CFSG.KC.Tab.table leaf (nextPow2 (max its.size 1)) 0)

open CFSG.Certificates.KB.Load CFSG.KC.Gz in
elab "#kc_list_gz " nm:ident path:str per:num size:num hash:num : command => do
  let b ← readPinnedGz path.getString size.getNat hash.getNat
  let L := nm.getId
  let its := items b
  let per := per.getNat
  let listT := mkApp (mkConst ``List [Level.zero]) natT
  withSync do
    let nk := (its.size + per - 1) / per
    for k in [0:nk] do
      let mut e := mkApp (mkConst ``List.nil [Level.zero]) natT
      let top := min its.size ((k + 1) * per)
      for jj in [0:top - k * per] do
        let j := top - 1 - jj
        let (lo, hi) := its[j]!
        e := mkApp3 (mkConst ``List.cons [Level.zero]) natT (lit (natLE b lo hi)) e
      addDef (L ++ Name.mkSimple s!"c{k}") listT e
