module


public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import CFSG.GroupTheory.CoprimeActionSupport.IndependentOrbitNormInjective

public section

namespace CFSG.LinearAlgebra.CoprimeActions.FixedLineFreeOrbitDimensionOne

theorem finrank_eq_one {F : Type*} [Field F] {A : Type*} [Group A] [Fintype A]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F A V) (E : Submodule F V) (hE : E ≠ ⊥)
    (hInd : iSupIndep (fun a : A => E.map (ρ a)))
    (hfix : Module.finrank F (Representation.invariants ρ) = 1) :
    Module.finrank F E = 1 := by
  set f := (∑ a : A, ρ a).comp E.subtype with hf
  have hinj : Function.Injective f := CFSG.GroupTheory.CoprimeActionSupport.IndependentOrbitNormInjective.injective ρ E hInd
  have hrange := CFSG.GroupTheory.CoprimeActionSupport.IndependentOrbitNormInjective.fixed_range ρ E
  have h1 : Module.finrank F E = Module.finrank F (LinearMap.range f) :=
    (LinearMap.finrank_range_of_inj hinj).symm
  have h2 : Module.finrank F (LinearMap.range f) ≤ 1 := by
    rw [← hfix]
    exact Submodule.finrank_mono (fun v hv => by
      rw [Representation.mem_invariants]; exact hrange hv)
  have h3 : 0 < Module.finrank F E := by
    rw [Module.finrank_pos_iff]
    exact (Submodule.nontrivial_iff_ne_bot).2 hE |> fun h => h
  omega

end CFSG.LinearAlgebra.CoprimeActions.FixedLineFreeOrbitDimensionOne
