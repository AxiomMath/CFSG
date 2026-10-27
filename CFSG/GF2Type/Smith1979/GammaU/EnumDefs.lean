module

public import CFSG.GF2Type.Smith1979.GammaU.ViolationDefs

public section

namespace CFSG.GF2Type.Smith1979.GammaU.Enum

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

@[expose] def enumGrp (gs : List (Array ℕ)) : List (Array ℕ) :=
  bfsClosure (fun x : Array ℕ => x) (gs.map fun g x => mulR x g) 100000 [idR]
    ((∅ : Std.HashSet (Array ℕ)).insert idR) []

@[expose] def closedCheck (gs X : List (Array ℕ)) : Bool :=
  let S := Std.HashSet.ofList X
  X.all fun x => gs.all fun g => S.contains (mulR x g)

@[expose] def commR (a b : Array ℕ) : Array ℕ :=
  mulR a (mulR b (mulR (Viol.invR a) (Viol.invR b)))

end CFSG.GF2Type.Smith1979.GammaU.Enum
