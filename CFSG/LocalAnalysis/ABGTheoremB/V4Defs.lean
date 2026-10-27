module

public import CFSG.LocalAnalysis.ABGTheoremB.V3Defs

public noncomputable section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open scoped Pointwise

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

structure IsV21Layer (J : Subgroup G) : Prop where
  le : J ≤ σ.L₀
  pCore_le : pCoreIn σ.p σ.N ≤ J
  sup_eq : σ.L₀ = J ⊔ σ.ON
  inf_eq : J ⊓ σ.ON = pCoreIn σ.p σ.N
  normal : σ.N ≤ Subgroup.normalizer (J : Set G)
  commutator_le : ⁅J, σ.ON⁆ ≤ pCoreIn σ.p σ.N
  sl2 : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = σ.q ∧
    ∃ ψ : J →* Matrix.SpecialLinearGroup (Fin 2) F, Function.Surjective ψ ∧
      ψ.ker = (pCoreIn σ.p σ.N).subgroupOf J

@[expose] def LemmaV45 (J : Subgroup G) : Prop :=
  ∀ W ∈ σ.familyW J, ∀ X : Subgroup G, σ.D ≤ Subgroup.normalizer (X : Set G) →
    W ≤ Subgroup.normalizer (X : Set G) →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card X → ℓ = σ.p ∨ ℓ ∣ Nat.card W) →
      (X = pCoreIn σ.p X ⊔ (X ⊓ σ.N) ∧
        X = pCoreIn σ.p X ⊔ (X ⊓ Subgroup.normalizer (W : Set G))) ∧
      ∃ P : Subgroup G, IsSylowOf σ.p P X ∧ P ≤ pCoreIn σ.p X ⊔ (X ⊓ σ.C)

omit [Finite G] in
theorem CorollaryV21.exists_isV21Layer {σ : Setting G} (h : σ.CorollaryV21) :
    ∃ J : Subgroup G, σ.IsV21Layer J := by
  obtain ⟨J, hle, hp, hsup, hinf, hnorm, hcomm, hsl⟩ := h.layer
  exact ⟨J, ⟨hle, hp, hsup, hinf, hnorm, hcomm, hsl⟩⟩

end Setting

end CFSG.ABGTheoremB
