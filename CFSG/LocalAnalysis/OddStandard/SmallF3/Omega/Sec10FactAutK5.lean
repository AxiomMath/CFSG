module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82FactAutK5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K1 K2 : Subgroup G),
    ⁅K1, K2⁆ = ⊥ → Nat.card ↥(K1 ⊔ K2) = 288 →
    Nonempty (↥K1 ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) →
    Nonempty (↥K2 ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) →
    ∀ Φ Ψ : Subgroup (MulAut ↥(K1 ⊔ K2)),
      Ψ ≤ Φ → IsPGroup 2 ↥Φ → Ψ.relIndex Φ = 2 → 64 ≤ Nat.card ↥Ψ →
      (∀ q : ↥(K1 ⊔ K2), (q : G) ∈ twoCoreIn (K1 ⊔ K2) → MulAut.conj q ∈ Ψ) →
      (∃ σ ∈ Ψ, ∀ k : ↥(K1 ⊔ K2), (k : G) ∈ K1 → ((σ k : ↥(K1 ⊔ K2)) : G) ∈ K2) →
        ∃ ψ ∈ Φ, ψ ∉ Ψ ∧ ψ * ψ = 1 ∧
          (∀ k : ↥(K1 ⊔ K2), (k : G) ∈ K1 → ((ψ k : ↥(K1 ⊔ K2)) : G) ∈ K1) ∧
          (∀ k : ↥(K1 ⊔ K2), (k : G) ∈ K2 → ψ k = k) ∧
          ¬ ∃ k : ↥(K1 ⊔ K2), (k : G) ∈ K1 ∧
            ∀ y : ↥(K1 ⊔ K2), (y : G) ∈ K1 → ((ψ y : ↥(K1 ⊔ K2)) : G) = k * y * k⁻¹

end CFSG.OddStandard.SmallF3.Omega
