module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Cent

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Assembly.LowTwoRank
  CFSG.GH74.KGroups.L3Eps.Uni
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped MatrixGroups commutatorElement

section Data

structure KAOuterData {ℓ f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData ℓ f F) {K : Type}
    [Group K]
    (θ : ↥(unitarySU ℓ f F 3) →* K) (σ : MulAut K) where
  Ψ : SL(2, ↥h.fixedField) →* ↥(unitarySU ℓ f F 3)
  fixed : ∀ S, σ (θ (Ψ S)) = θ (Ψ S)
  irr : ∀ W : Submodule F (Fin 3 → F),
    (∀ S, ∀ v ∈ W, ((Ψ S : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤
  comm : ∀ T : Matrix (Fin 3) (Fin 3) F,
    (∀ S, T * ((Ψ S : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((Ψ S : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * T) →
        ∃ c : F, T = c • (1 : Matrix (Fin 3) (Fin 3) F)
  tr : ∀ τ : F ≃+* F, (∀ S, τ (Matrix.trace ((Ψ S : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) =
    Matrix.trace ((Ψ S : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) → τ = 1 ∨ ∀ c, τ c = h.bar c
  centOK : CentOK ℓ f Ψ.range
  card : Nat.card ↥h.fixedField = ℓ ^ f
  ker : ∀ S, θ (Ψ S) = 1 → S = 1 ∨ S = -1
  negone : Ψ (-1) = 1

end Data

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
