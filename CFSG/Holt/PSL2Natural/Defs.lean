module

public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.Holt

open scoped LinearAlgebra.Projectivization

@[expose] def IsNaturalPSL2 {Δ : Type*} (K : Subgroup (Equiv.Perm Δ)) (n : ℕ) : Prop :=
  ∃ (φ : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n) ≃* K)
    (ψ : ℙ (GaloisField 2 n) (Fin 2 → GaloisField 2 n) ≃ Δ),
    ∀ (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n))
      (p : ℙ (GaloisField 2 n) (Fin 2 → GaloisField 2 n)),
      ψ (g • p) = (φ g : Equiv.Perm Δ) (ψ p)

end CFSG.Holt
