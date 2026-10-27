module

public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.Certificates.WordSubgroup
public meta import CFSG.LieType.Multipliers.U62Bridge
public meta import CFSG.LieType.Multipliers.U62Kernel
public meta import CFSG.LieType.Multipliers.U62Data
public meta import CFSG.LieType.Multipliers.U62Action
public meta import CFSG.LieType.Multipliers.CoverWords
public meta import CFSG.Certificates.WordSubgroup
public meta import Certificates.Data.CFSGNative.F4.T46Simple
public meta import Certificates.Data.CFSGNative.Fi22.Local
public meta import Certificates.Data.CFSGNative.Th.Tables
public import CFSG.LieType.Multipliers.U62Action

public section

namespace CFSG.EvenSmallLie.UnitarySix

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U62 CFSG.CosetTable CFSG.F4.Native
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi22.Native

@[expose] def deltaWords : List (List (Fin 5 × Bool)) :=
  [[(0, true)], [(1, true)], [(2, true)], [(3, true)], [(2, true), (4, true), (2, false)]]

@[expose] def muWord : List (Fin 5 × Bool) :=
  substWord deltaWords (commWords (coverPairs 4)) ++ [(2, true), (4, false), (2, false)]

@[expose] def deltaKerTwo : List (Fin 5 × Bool) := substWord deltaWords kerTwo

@[expose] def deltaKerSix : List (Fin 5 × Bool) := substWord deltaWords kerSix

@[expose] def zWord (a b c : ℕ) : List (Fin 5 × Bool) :=
  (List.replicate a kerThree).flatten ++
    ((List.replicate b kerTwo).flatten ++ (List.replicate c kerTwo').flatten)

@[expose] def zTriples : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 0), (0, 0, 1), (0, 1, 0), (0, 1, 1), (1, 0, 0), (1, 0, 1), (1, 1, 0), (1, 1, 1),
    (2, 0, 0), (2, 0, 1), (2, 1, 0), (2, 1, 1)]

@[expose] def exclWords (u : List (Fin 5 × Bool)) (t : ℕ × ℕ × ℕ) :
    List (List (Fin 5 × Bool)) :=
  (zTriples.filter (· ≠ t)).map fun p => u ++ FreeGroup.invRev (zWord p.1 p.2.1 p.2.2)

@[expose] def obsMoveWords : List (List (Fin 5 × Bool)) :=
  exclWords muWord (0, 0, 0) ++ exclWords deltaKerTwo (0, 1, 1) ++
    exclWords deltaKerSix (2, 1, 0)

@[expose] def deltaRelCheck : Bool :=
  rels.all fun r => t46FixAll (wordT 693 t46Gen (U62.expand (substWord deltaWords r)))

end CFSG.EvenSmallLie.UnitarySix
