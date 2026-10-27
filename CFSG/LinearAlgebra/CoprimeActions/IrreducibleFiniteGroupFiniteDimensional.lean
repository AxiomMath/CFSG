module


public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic

public section

open scoped MonoidAlgebra

namespace CFSG.LinearAlgebra.CoprimeActions.IrreducibleFiniteGroupFiniteDimensional

theorem finiteDimensional_of_irreducible {F G V : Type*} [Field F] [Group G] [Finite G]
    [AddCommGroup V] [Module F V] (ρ : Representation F G V) (h : ρ.IsIrreducible) :
    FiniteDimensional F V := by
  have : IsSimpleModule F[G] ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp h
  have : Module.Finite F[G] ρ.asModule := inferInstance
  have : Module.Finite F ρ.asModule := Module.Finite.trans F[G] ρ.asModule
  exact this

end CFSG.LinearAlgebra.CoprimeActions.IrreducibleFiniteGroupFiniteDimensional
