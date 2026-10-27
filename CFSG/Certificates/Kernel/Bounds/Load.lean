module

public meta import Lean
public import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Common.Tab

open Lean Elab Command

public section

namespace CFSG.Certificates.KB.Load

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

meta def u32 (b : ByteArray) (i : Nat) : Nat :=
  b[i]!.toNat + (b[i+1]!.toNat <<< 8) + (b[i+2]!.toNat <<< 16) + (b[i+3]!.toNat <<< 24)

meta def addDef (name : Name) (type value : Expr) : CoreM Unit :=
  addDecl (forceExpose := true) <| .defnDecl
    { name, levelParams := [], type, value, hints := .regular 0, safety := .safe }

meta def natT (_ : Unit := ()) : Expr := mkConst ``Nat
meta def fnT (_ : Unit := ()) : Expr := mkForall `i .default natT natT
meta def lit (n : Nat) : Expr := mkRawNatLit n

meta def nextPow2 (n : Nat) : Nat := Id.run do
  let mut p := 1
  while p < n do p := 2 * p
  return p

meta def items (b : ByteArray) : Array (Nat × Nat) := Id.run do
  let mut out := #[]
  let mut i := 0
  while i + 4 ≤ b.size do
    let n := u32 b i
    out := out.push (i + 4, i + 4 + n)
    i := i + 4 + n
  return out

meta def withSync (x : CoreM Unit) : CommandElabM Unit :=
  liftCoreM <| withOptions (Elab.async.set · false) x

meta def readPinned (rel : String) (size hash : Nat) : CommandElabM ByteArray := do
  let some dir := (System.FilePath.mk (← getFileName)).parent
    | throwError "cannot compute the directory of {← getFileName}"
  let path := dir / rel
  let b ← IO.FS.readBinFile path
  unless b.size == size && b.hash.toNat == hash do
    throwError "data file {path}: size {b.size} hash {b.hash.toNat}, pinned size {size} hash {hash}"
  return b

end CFSG.Certificates.KB.Load

open CFSG.Certificates.KB.Load in
elab "#kc_blocked " nm:ident "include_bytes" path:str logRecs:num logStride:num mask:num
    size:num hash:num : command => do
  let b ← readPinned path.getString size.getNat hash.getNat
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

open CFSG.Certificates.KB.Load in
elab "#kc_items " nm:ident "include_bytes" path:str size:num hash:num : command => do
  let b ← readPinned path.getString size.getNat hash.getNat
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

open CFSG.Certificates.KB.Load in
elab "#kc_list " nm:ident "include_bytes" path:str per:num size:num hash:num : command => do
  let b ← readPinned path.getString size.getNat hash.getNat
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

end
