module

public import CFSG.ClassicalInvolution.Q3.Q3MFODOrb

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ClassicalInvolution.Q3
open CFSG.LieType.Universal.Spin (spinAction quadPlus)

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)

@[expose] def FKMultNegOne : Prop :=
  ∀ α : MulAut (spinGroup Q₄), α * α = 1 → Q3MFOD.Pres α →
    ∀ (a : (Fin 4 ⊕ Fin 4 → GaloisField 3 1) ≃ₗ[GaloisField 3 1] (Fin 4 ⊕ Fin 4 → GaloisField 3 1))
      (s : GaloisField 3 1), (∀ v, Q₄ (a v) = -Q₄ v) → (∀ v, a (a v) = s • v) →
      (∀ x, spinAction Q₄ (α x) = a * spinAction Q₄ x * a⁻¹) →
      ∃ σ : MulAut (spinGroup Q₄), Q3MFOD.Pres (σ * α * σ⁻¹) ∧
        ∃ (a' : (Fin 4 ⊕ Fin 4 → GaloisField 3 1) ≃ₗ[GaloisField 3 1]
            (Fin 4 ⊕ Fin 4 → GaloisField 3 1)) (s' : GaloisField 3 1),
          (∀ v, Q₄ (a' v) = Q₄ v) ∧ (∀ v, a' (a' v) = s' • v) ∧
            ∀ x, spinAction Q₄ ((σ * α * σ⁻¹) x) = a' * spinAction Q₄ x * a'⁻¹

end CFSG.OddStandard.SmallF3.Omega
