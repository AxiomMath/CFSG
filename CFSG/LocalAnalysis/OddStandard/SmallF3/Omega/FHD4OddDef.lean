module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFD4O

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG CFSG.Blueprint CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
  CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open scoped Pointwise

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)

local notation "V₈" => Fin 4 ⊕ Fin 4 → GaloisField 3 1

@[expose] def FHSimFamO (m s : 𝔽₃) : Prop :=
  ∀ a : V₈ ≃ₗ[𝔽₃] V₈, (∀ v, Q₄ (a v) = m * Q₄ v) → (∀ v, a (a v) = s • v) →
    ∀ β : MulAut (D4P 𝔽₃), Odd (orderOf β) →
      (∀ x : spinGroup Q₄, spinAction Q₄ x * a = a * spinAction Q₄ x →
        Odd (orderOf (Q3T.d4Proj 𝔽₃ x)) → β (Q3T.d4Proj 𝔽₃ x) = Q3T.d4Proj 𝔽₃ x) →
        β • statedPointFamily (coe_quadPlus 4 𝔽₃) = statedPointFamily (coe_quadPlus 4 𝔽₃)

end CFSG.OddStandard.SmallF3.Omega
