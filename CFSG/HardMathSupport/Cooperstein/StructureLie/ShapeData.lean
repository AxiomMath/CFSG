module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLHeart
public import CFSG.LocalAnalysis.ComponentInitial.LinearIsometry
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.ComponentClassification.OutcomeLocal CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

@[expose] def orthGL {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (Q : QuadraticForm (ZMod 2) W) : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W) :=
  (TauCeti.QuadraticMap.orthogonalGroup Q).comap
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).toMonoidHom

@[expose] def ShapeOut (Y : Type) [Group Y] : Prop :=
  (∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : FiniteDimensional (ZMod 2) W)
      (Q : QuadraticForm (ZMod 2) W), (QuadraticMap.polarBilin Q).Nondegenerate ∧
        Nonempty (Y ≃* ↥⁅orthGL Q, orthGL Q⁆)) ∨
  (∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : FiniteDimensional (ZMod 2) W)
      (f : LinearMap.BilinForm (ZMod 2) W), Module.finrank (ZMod 2) W = 4 ∧ f.Nondegenerate ∧
        f.IsAlt ∧ Nonempty (Y ≃* ↥⁅bilinIsometryGroup f, bilinIsometryGroup f⁆)) ∨
  ∃ m : ℕ, 5 ≤ m ∧ Nonempty (Y ≃* alternatingGroup (Fin m))

end CFSG.HardMathSupport.Cooperstein.StructureLie
