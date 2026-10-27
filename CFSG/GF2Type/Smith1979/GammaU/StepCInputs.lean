module

public import CFSG.GF2Type.Smith1979.GammaU.StepAInputs

public section

namespace CFSG.GF2Type.Smith1979.GammaU.StepA

open CFSG.GF2Type.Smith1979.GammaU

@[expose] def theta0R : Array ℕ := #[64, 128, 256, 512, 1024, 2048, 65, 130, 260, 520, 1040, 2080]

@[expose] def colPts (s : Array ℕ) : List ℕ :=
  let S := spanList d0
  let im := (List.range 4096).map fun n => appN s n ^^^ n
  S.filter fun e => e != 0 && !q0b e && e != a0 && e != theta0N a0 &&
    e != (a0 ^^^ theta0N a0) && im.contains e

@[expose] def unitaryElts (i : ℕ) : List (Array ℕ) :=
  (compOf i).filter fun s => s != idR && unitaryN s

@[expose] def orbitOf (gens : List (Array ℕ)) (p : ℕ) : List ℕ :=
  bfsClosure id (gens.map appN) 4096 [p] ((∅ : Std.HashSet ℕ).insert p) []

end CFSG.GF2Type.Smith1979.GammaU.StepA
