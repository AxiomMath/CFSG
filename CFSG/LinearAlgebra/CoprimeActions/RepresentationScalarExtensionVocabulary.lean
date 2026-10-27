module


public import Mathlib.RepresentationTheory.Basic

public section

namespace CFSG.LinearAlgebra.CoprimeActions.RepresentationScalarExtensionVocabulary

open TensorProduct

variable {F K G V : Type*} [Field F] [Field K] [Algebra F K] [Monoid G]
  [AddCommGroup V] [Module F V]

@[expose] noncomputable def extend (ρ : Representation F G V) : Representation K G (K
⊗[F] V) :=
  (Module.End.baseChangeHom F K V).toMonoidHom.comp ρ

theorem extend_tmul (ρ : Representation F G V) (g : G) (k : K) (v : V) :
    extend (K := K) ρ g (k ⊗ₜ[F] v) = k ⊗ₜ[F] ρ g v := by
  exact _root_.LinearMap.baseChange_tmul (A := K) (ρ g) k v

theorem extend_apply (ρ : Representation F G V) (g : G) :
    extend (K := K) ρ g = (ρ g).baseChange K := rfl

end CFSG.LinearAlgebra.CoprimeActions.RepresentationScalarExtensionVocabulary
