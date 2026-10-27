module


public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import CFSG.LinearAlgebra.CoprimeActions.RepresentationScalarExtensionVocabulary
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

public section

namespace CFSG.LinearAlgebra.CoprimeActions.ScalarExtendedRepresentationFaithful

open TensorProduct CFSG.LinearAlgebra.CoprimeActions.RepresentationScalarExtensionVocabulary

variable {F K G V : Type*} [Field F] [Field K] [Algebra F K] [Group G]
  [AddCommGroup V] [Module F V]

theorem faithful (ρ : Representation F G V) (h : Function.Injective ρ) :
    Function.Injective (extend (K := K) ρ) := by
  intro g h' e
  apply h
  apply LinearMap.baseChangeHom_injective F V K
  simpa [extend_apply] using e

end CFSG.LinearAlgebra.CoprimeActions.ScalarExtendedRepresentationFaithful
