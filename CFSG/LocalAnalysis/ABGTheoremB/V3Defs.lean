module

public import CFSG.LocalAnalysis.ABGTheoremB.Setting

public noncomputable section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open scoped Pointwise

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

structure CorollaryV21 : Prop where
  sylow_centralized_or_inverted : ∀ r : ℕ, r.Prime → ∀ R : Subgroup G, IsSylowOf r R σ.ON →
    σ.T ≤ Subgroup.normalizer (R : Set G) →
      (∀ y ∈ R, σ.x₂ * y * σ.x₂⁻¹ * y⁻¹ ∈ pCoreIn σ.p σ.N) ∨
        ∀ y ∈ R, σ.x₂ * y * σ.x₂⁻¹ * y ∈ pCoreIn σ.p σ.N
  layer : ∃ J : Subgroup G, J ≤ σ.L₀ ∧ pCoreIn σ.p σ.N ≤ J ∧ σ.L₀ = J ⊔ σ.ON ∧
    J ⊓ σ.ON = pCoreIn σ.p σ.N ∧ σ.N ≤ Subgroup.normalizer (J : Set G) ∧
    ⁅J, σ.ON⁆ ≤ pCoreIn σ.p σ.N ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = σ.q ∧
      ∃ ψ : J →* Matrix.SpecialLinearGroup (Fin 2) F, Function.Surjective ψ ∧
        ψ.ker = (pCoreIn σ.p σ.N).subgroupOf J

@[expose] def familyW (J : Subgroup G) : Set (Subgroup G) :=
  {W | W ≤ J ∧ σ.D ≤ Subgroup.normalizer (W : Set G) ∧ W ⊓ pCoreIn σ.p σ.N = ⊥ ∧
    W ⊔ pCoreIn σ.p σ.N = oddCoreIn σ.C ⊓ J ⊔ pCoreIn σ.p σ.N}

@[expose] def PropV41 (J : Subgroup G) : Prop :=
  ∀ H : Subgroup G, σ.D ≤ H → oddCoreIn H ≠ ⊥ → ∀ P : Subgroup G, IsSylowOf σ.p P σ.C →
    σ.D ≤ Subgroup.normalizer (P : Set G) → P ≤ H → ∀ W ∈ σ.familyW J, W ≤ H →
    ∀ V ∈ signalizersPerm H σ.D W σ.p, P ≤ V →
      (∃ U ∈ signalizersPerm H σ.D W σ.p, V ≤ U ∧ U ∈ maximals (signalizers H σ.D σ.p) ∧
        IsSylowOf σ.p (U ⊓ oddCoreIn H) (oddCoreIn H)) ∧
      ∀ U₁ ∈ signalizersPerm H σ.D W σ.p, ∀ U₂ ∈ signalizersPerm H σ.D W σ.p,
        U₁ ∈ maximals (signalizers H σ.D σ.p) → U₂ ∈ maximals (signalizers H σ.D σ.p) →
        V ≤ U₁ → V ≤ U₂ → ∃ b ∈ σ.C ⊓ Subgroup.normalizer (W : Set G) ⊓
          Subgroup.centralizer (σ.D : Set G), U₁.map (MulAut.conj b).toMonoidHom = U₂

end Setting

end CFSG.ABGTheoremB
