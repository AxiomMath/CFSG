module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.DataRoot

open Lean Elab Command

namespace CFSG.KC.Repo

meta def pkgRoot : CommandElabM System.FilePath := do
  let m ← getMainModule
  if m.isAnonymous || m == `_stdin then return "."
  let mut p := System.FilePath.mk (← getFileName)
  for _ in m.components do
    p := p.parent.getD "."
  return if p.toString.isEmpty then "." else p

end CFSG.KC.Repo

elab "#kc_repo " c:command : command => do
  CFSG.KC.withDataRoot (← CFSG.KC.Repo.pkgRoot) (elabCommand c)
