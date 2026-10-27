module

public meta import Lean

open Lean

public section

namespace CFSG.KC

meta def addThmDecl (v : TheoremVal) : CoreM Unit := do
  let v := if (← getOptions).getBool `debug.proofAsSorry && (← getEnv).contains ``sorryAx then
    { v with value := mkApp2 (mkConst ``sorryAx [levelZero]) v.type (mkConst ``Bool.false) } else v
  addDecl <| .thmDecl v

end CFSG.KC

end
