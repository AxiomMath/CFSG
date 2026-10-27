module

public import Mathlib
public import CFSG.GH74.E2.Shapes
public import CFSG.GH74.KGroups.L33
public import CFSG.GH74.KGroups.Checks
public meta import Mathlib
public meta import CFSG.GH74.KGroups.L33
public import CFSG.GH74.SectionalRank
public import CFSG.GH74.Statements
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.GH74.E2

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups
section Checks

variable {n : ℕ}

@[expose] def isOuterInv (QP : RawSchreierDatum n) (τ : Equiv.Perm (Fin n)) : Bool :=
  decide (τ ^ 2 = 1) && !QP.sift τ 0

@[expose] def outerConjAt (QP : RawSchreierDatum n) (L : List (Equiv.Perm (Fin n)))
    (τ0 : Equiv.Perm (Fin n)) : Bool :=
  isOuterInv QP τ0 && L.all fun τ =>
    !isOuterInv QP τ || L.any fun σ => decide (σ * τ0 * σ⁻¹ = τ)

@[expose] def outerConjCheck (QP : RawSchreierDatum n) (L : List (Equiv.Perm (Fin n))) : Bool :=
  L.any (outerConjAt QP L)

@[expose] def outerCommAt (C : List (Equiv.Perm (Fin n))) : Bool :=
  C.any fun a => C.any fun b =>
    decide ((a * b * a⁻¹ * b⁻¹) ^ 2 = 1) && decide (a * b * a⁻¹ * b⁻¹ ≠ 1)

@[expose] def outerCommCheck (QP : RawSchreierDatum n) (LA LP : List (Equiv.Perm (Fin n))) :
    Bool :=
  LA.all fun τ => !isOuterInv QP τ || outerCommAt (LP.filter fun g => decide (g * τ = τ * g))

end Checks

end CFSG.GH74.E2
