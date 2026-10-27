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
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.CoverActionDataInputs
public import Certificates.Certificate3143

public section

namespace CFSG.EvenSmallLie.UnitarySix

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U62 CFSG.CosetTable CFSG.F4.Native
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi22.Native

@[expose] def commGenWords : List (List (Fin 5 × Bool)) :=
  [commWords (coverPairs 0), commWords (coverPairs 1), commWords (coverPairs 2),
    commWords (coverPairs 3), commWords (coverPairs 4)]

@[expose] def obsWordA : List (Fin 5 × Bool) := substWord commGenWords kerTwo

@[expose] def obsWordB : List (Fin 5 × Bool) := substWord commGenWords kerSix

@[expose] def obsWordA' : List (Fin 5 × Bool) := substWord deltaWords obsWordA

@[expose] def obsWordB' : List (Fin 5 × Bool) := substWord deltaWords obsWordB

theorem deltaRel_check : deltaRelCheck = true :=
  Certificates.certificate3143.1

theorem obs_check :
    ∃ (E : Type) (_ : Group E) (ψ : PG 5 coverWs →* E),
      ∀ u ∈ obsMoveWords, ψ (PresentedGroup.mk _ (FreeGroup.mk u)) ≠ 1 :=
  Certificates.certificate3143.2

end CFSG.EvenSmallLie.UnitarySix
