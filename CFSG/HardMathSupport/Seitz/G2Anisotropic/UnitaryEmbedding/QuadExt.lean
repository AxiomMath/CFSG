module

public import Mathlib.FieldTheory.Finite.Extension

public section

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding

theorem exists_quadratic_frobenius_all (K : Type) [Field K] [Finite K] :
    ∃ (K₂ : Type) (_ : Field K₂) (_ : Algebra K K₂), Module.finrank K K₂ = 2 ∧
      ∃ σ : K₂ ≃+* K₂, ∀ c, σ c = c ^ Nat.card K := by
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  refine ⟨FiniteField.Extension K (ringChar K) 2, inferInstance, inferInstance,
    FiniteField.finrank_extension K (ringChar K) 2,
    (FiniteField.Extension.frob K (ringChar K) 2).toRingEquiv, fun c => ?_⟩
  exact FiniteField.Extension.frob_apply K (ringChar K) 2
