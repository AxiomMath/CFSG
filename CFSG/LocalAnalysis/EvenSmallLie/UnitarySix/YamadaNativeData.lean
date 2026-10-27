
module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaNativeDataBase

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeData

public section

namespace CFSG.EvenSmallLie.UnitarySix.Yamada

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native

@[expose] def alphaOne
    : Equiv.Perm (Fin 693) := evalCodes aGens [2, 3]

@[expose] def kappaOne : Equiv.Perm (Fin 693) := evalCodes kGens [3]

@[expose] def alphaTwo
    : Equiv.Perm (Fin 693) := evalCodes aGens [3, 6]

@[expose] def kappaTwo
    : Equiv.Perm (Fin 693) := evalCodes kGens [1, 3, 1, 3, -1, 3, -1]

@[expose] def commCheck : Bool :=
  commT 693 (toTable kappaOne) (toTable j1) &&
    tblEq 693 (toTable (alphaOne * kappaOne * alphaOne⁻¹ * kappaOne⁻¹)) (toTable j1) &&
    commT 693 (toTable kappaTwo) (toTable j2) &&
    tblEq 693 (toTable (alphaTwo * kappaTwo * alphaTwo⁻¹ * kappaTwo⁻¹)) (toTable j2)

@[expose] def orbitElt (i : ℕ) : Equiv.Perm (Fin 693) :=
  evalCodes kGens (orbitWords.getD i []) * j1 * (evalCodes kGens (orbitWords.getD i []))⁻¹

@[expose] def stabElt
    (m : ℕ) : Equiv.Perm (Fin 693) := evalCodes kGens (stabWords.getD m [])

@[expose] def transCheck : Bool :=
  (kGens ++ kGens.map (·⁻¹)).all (fun g => (List.range 21).all fun i =>
      (List.range 21).any fun j =>
        tblEq 693 (toTable (g * orbitElt i * g⁻¹)) (toTable (orbitElt j))) &&
    (List.range 21).all fun m => m == 0 ||
      (commT 693 (toTable (stabElt m)) (toTable j1) &&
        tblEq 693 (toTable (stabElt m * orbitElt 1 * (stabElt m)⁻¹)) (toTable (orbitElt m)))

end CFSG.EvenSmallLie.UnitarySix.Yamada
