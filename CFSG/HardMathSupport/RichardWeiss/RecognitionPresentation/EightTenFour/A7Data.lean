module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour

open Equiv Equiv.Perm

abbrev A7 : Type := alternatingGroup (Fin 7)

@[expose, reducible] def IsClosedFin (S : Finset A7) : Prop :=
  1 ∈ S ∧ (∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) ∧ ∀ x ∈ S, x⁻¹ ∈ S

instance (S : Finset A7) : Decidable (IsClosedFin S) :=
  have _h1 : Decidable (1 ∈ S) := inferInstance
  have _h2 : Decidable (∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) := inferInstance
  have _h3 : Decidable (∀ x ∈ S, x⁻¹ ∈ S) := inferInstance
  instDecidableAnd

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour
