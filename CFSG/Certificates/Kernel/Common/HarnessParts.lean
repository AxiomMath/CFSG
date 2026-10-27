module

public meta import Lean
public import CFSG.Certificates.Kernel.Common.Harness
meta import all CFSG.Certificates.Kernel.Common.Harness

open Lean Elab Command

namespace CFSG.KC.Load

public meta def readPinnedParts {m : Type → Type} [Monad m] [MonadOptions m] [MonadLiftT IO m]
    (parts : Array (String × Nat × Nat)) (size hash : Nat) : m ByteArray := do
  let mut b := ByteArray.empty
  for (p, s, h) in parts do
    b := b ++ (← readPinned p s h)
  monadLift (m := IO) do
  let h := b.hash.toNat
  unless b.size == size && h == hash do
    let msg := s!"data parts {parts.map (·.1)}: size {b.size} hash {h}, \
      pinned size {size} hash {hash}"
    throw (IO.userError msg)
  return b

end CFSG.KC.Load

declare_syntax_cat kcPart
syntax "(" str num num ")" : kcPart

public meta def CFSG.KC.Load.partsOf (ps : Array (TSyntax `kcPart)) :
    Array (String × Nat × Nat) :=
  ps.map fun p => ((⟨p.raw[1]⟩ : TSyntax `str).getString, (⟨p.raw[2]⟩ : TSyntax `num).getNat,
    (⟨p.raw[3]⟩ : TSyntax `num).getNat)

open CFSG.KC.Load in
elab "#kc_ktree_parts " pre:ident id:ident lb:num fan:num size:num hash:num ps:kcPart+ :
    command => do
  let b ← readPinnedParts (partsOf ps) size.getNat hash.getNat
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
