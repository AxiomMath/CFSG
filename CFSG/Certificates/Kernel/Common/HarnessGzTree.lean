module

public meta import Lean
public import CFSG.Certificates.Kernel.Common.HarnessGz
meta import all CFSG.Certificates.Kernel.Common.Harness
meta import all CFSG.Certificates.Kernel.Common.HarnessGz

open Lean Elab Command

open CFSG.KC.Load CFSG.KC.Gz in
elab "#kc_ktree_gz " pre:ident id:ident path:str lb:num fan:num size:num hash:num : command => do
  let b ← readPinnedGz path.getString size.getNat hash.getNat
  let F := pre.getId ++ id.getId
  let leafBytes := lb.getNat
  let nLeaves := (b.size + leafBytes - 1) / leafBytes
  let h := Nat.log2 (2 * nLeaves - 1)
  let leafName := fun k => if k < nLeaves then F ++ Name.mkSimple s!"L{k}" else F ++ `Z
  withSync do
    addDef (F ++ `Z) natE (mkRawNatLit 0) true
    for k in [0:nLeaves] do
      let s := k * leafBytes
      addDef (leafName k) natE (mkRawNatLit (natLE b s (min b.size (s + leafBytes)))) true
    addKTreeNodes leafName F 0 h fan.getNat
