module

public meta import Lean

open Lean Elab Term

elab "include_str_chunks " path:str kN:num : term => do
  let ctx ← readThe Lean.Core.Context
  let some srcDir := (System.FilePath.mk ctx.fileName).parent
    | throwError "include_str_chunks: cannot compute parent directory of `{ctx.fileName}`"
  let s ← IO.FS.readFile (srcDir / path.getString)
  let k := kN.getNat
  if k == 0 then throwError "include_str_chunks: the chunk size is 0"
  let cs := s.toList.toArray
  let n := max 1 ((cs.size + k - 1) / k)
  let piece := fun (j : Nat) =>
    mkStrLit (String.ofList (cs.extract (j * k) (min cs.size (j * k + k))).toList)
  let app ← elabTerm (← `(fun (a b : String) => a ++ b)) none
  synthesizeSyntheticMVarsNoPostponing
  let app ← instantiateMVars app
  let mut t := piece (n - 1)
  for j' in [1:n] do
    t := (mkApp2 app (piece (n - 1 - j')) t).headBeta
  return t
