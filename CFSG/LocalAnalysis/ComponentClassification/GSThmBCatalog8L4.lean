module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8Sp4

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

@[expose] def IsSec82LType (Y : Type) [Group Y] (p f : ℕ) : Prop :=
  Blueprint.LieModel Y .PSL 4 p f ∨ Blueprint.LieModel Y .PSU 4 p f ∨
    Nonempty (Y ≃* alternatingGroup (Fin 10))

@[expose] def CF82Inner : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    IsSimpleGroup ↥(generalizedFitting H) →
    centralizer (generalizedFitting H : Set H) = ⊥ →
    IsSec82LType ↥(generalizedFitting H) p f →
    ∀ α β ξ : H, α * α = 1 → α = ⁅β, ξ⁆ →
    ∀ J₁ : Subgroup H, J₁ ≤ centralizer ({α} : Set H) →
      IsPComponent 2 (J₁.subgroupOf (centralizer ({α} : Set H))) →
      IsSec8JType (↥J₁ ⧸ pPrimeCore 2 ↥J₁) p f →
      β ∈ coreActionKernel J₁ → ξ ∈ coreActionKernel J₁ →
      α ∈ generalizedFitting H ∧
        (Blueprint.LieModel ↥(generalizedFitting H) .PSL 4 p f → p ^ f % 4 = 3) ∧
        (Blueprint.LieModel ↥(generalizedFitting H) .PSU 4 p f → p ^ f % 4 = 1)

@[expose] def CF82Cover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    ∀ Y : Subgroup G, IsQuasisimple ↥Y → center ↥Y ≠ ⊥ →
    IsSec82LType (↥Y ⧸ center ↥Y) p f →
    ∀ t : G, t * t = 1 → t ∈ normalizer (Y : Set G) →
    (∃ y₀ ∈ Y, ∀ w ∈ Y, t * w * t⁻¹ = y₀ * w * y₀⁻¹) →
    ∀ M : Subgroup G, M ≤ Y ⊓ centralizer ({t} : Set G) →
      IsPComponent 2 (M.subgroupOf (Y ⊓ centralizer ({t} : Set G))) →
      ¬ IsSec8JType (↥M ⧸ pPrimeCore 2 ↥M) p f

end CFSG.ComponentClassification.GSThmB
