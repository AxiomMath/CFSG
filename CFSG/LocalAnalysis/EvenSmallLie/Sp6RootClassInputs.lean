module

public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JConditionInputs
public meta import CFSG.LocalAnalysis.EvenSmallLie.Sp6JConditionInputs
public import CFSG.Sporadic.Schreier.CountSpec
public meta import CFSG.Sporadic.Schreier.CountSpec

public section

namespace CFSG.EvenSmallLie.Sp6

open CFSG.Certificates CFSG.Certificates.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native
open CFSG.ComponentClassification.M12Cover

set_option compiler.extract_closed false

@[expose] def sp6SylowP1 (_ : Unit := ()) : Equiv.Perm (Fin 36) :=
  evalCodes sp6CentGens2 [1, 1, 1, 1]

@[expose] def sp6SylowP2 (_ : Unit := ()) : Equiv.Perm (Fin 36) :=
  evalCodes sp6CentGens2 [1, 1, 2, 1, 1, 2]

@[expose] def sp6SylowPerms (_ : Unit := ()) : List (Equiv.Perm (Fin 36)) :=
  let p₁ := sp6SylowP1 ()
  let p₂ := sp6SylowP2 ()
  (List.range 3).flatMap fun i => (List.range 3).map fun j => p₁ ^ i * p₂ ^ j

@[expose] def sp6SylowCheck (_ : Unit := ()) : Bool :=
  ordTest 36 3 (toTable (sp6SylowP1 ())) && ordTest 36 3 (toTable (sp6SylowP2 ())) &&
    commT 36 (toTable (sp6SylowP1 ())) (toTable (sp6SylowP2 ()))

@[expose] def sp6SylowTabs (_ : Unit := ()) : List (Table × Table) :=
  (sp6SylowPerms ()).map fun q => (toTable q, toTable q⁻¹)

@[expose] def sp6K1Test (qt : List (Table × Table)) (T : Table) : Bool :=
  ordTest 36 2 T && qt.all fun p => commT 36 T (conjT 36 p.1 p.2 T)

@[expose] def sp6K1Count (_ : Unit := ()) : Nat :=
  countProducts 36 (sp6K1Test (sp6SylowTabs ())) (levelTables sp6CentQ2)
    (toTable (1 : Equiv.Perm (Fin 36)))

@[expose] def sp6ClassTabs (_ : Unit := ()) : List Table :=
  (conjClosure 36 (listTables sp6Gens) (listTables (sp6Gens.map (·⁻¹))) (toTable sp6Rep1)
    4000).1.toList

@[expose] def sp6Wit3 : List ℤ := [2, 2]

@[expose] def sp6Wit4 : List ℤ := [2, 2, 2]

@[expose] def sp6K2Check (_ : Unit := ()) : Bool :=
  let cl := sp6ClassTabs ()
  let gs := listTables sp6Gens
  let gis := listTables (sp6Gens.map (·⁻¹))
  let w₃ := evalCodes sp6Gens sp6Wit3
  let w₄ := evalCodes sp6Gens sp6Wit4
  cl.any (tblEq 36 (toTable sp6Rep1)) &&
  (List.range gs.size).all (fun l =>
    cl.all fun T => cl.any (tblEq 36 (conjT 36 gs[l]! gis[l]! T)) &&
      cl.any (tblEq 36 (conjT 36 gis[l]! gs[l]! T))) &&
  cl.all (fun T₁ => cl.all fun T₂ => !(ordTest 36 4 (compT 36 T₁ T₂))) &&
  ordTest 36 5 (compT 36 (toTable sp6Rep3)
    (conjT 36 (toTable w₃) (toTable w₃⁻¹) (toTable sp6Rep3))) &&
  ordTest 36 6 (compT 36 (toTable sp6Rep4)
    (conjT 36 (toTable w₄) (toTable w₄⁻¹) (toTable sp6Rep4)))

end CFSG.EvenSmallLie.Sp6
