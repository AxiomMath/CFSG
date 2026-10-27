module

public meta import Lean

open Lean Elab Command

namespace CFSG.KC

public meta def withDataRoot {α : Type} (root : System.FilePath) (x : CommandElabM α) : CommandElabM α :=
  withScope (fun sc => { sc with opts := sc.opts.set `cfsg.kc.dataRoot root.toString }) x

public meta def dataRoot {m : Type → Type} [Monad m] [MonadOptions m] [MonadLiftT IO m] :
    m System.FilePath := do
  match (← getOptions).get? (α := String) `cfsg.kc.dataRoot with
  | some r => return r
  | _ => monadLift (throw (IO.userError "no data root: data files are read under `#kc_repo` \
      (see the docstring of CFSG/Certificates/Kernel/Common/Repo.lean)") : IO System.FilePath)

end CFSG.KC
