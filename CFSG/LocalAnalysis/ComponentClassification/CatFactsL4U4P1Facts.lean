module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Cent

public section

namespace CFSG.ComponentClassification.HarrisLit.P1

open CFSG Subgroup

structure P1ModelFacts (S : Type) [Group S] : Prop where
  inner : ∀ s : S, orderOf s = 2 →
    Nat.card ↥(Q81.oddPart (centralizer {s})) ∣ 288 ∨
      Nat.card ↥(Q81.oddPart (centralizer {s})) = 360
  aut : ∀ (α β : MulAut S) (L : Subgroup S) (ℓ : S), orderOf α = 2 → orderOf β = 2 →
    α * β = β * α → Nat.card ↥L = 360 → (∀ y ∈ L, α y = y) →
    (∀ c : S, α c = c → ∀ y ∈ L, c * y * c⁻¹ ∈ L) → ℓ ∈ L → orderOf ℓ = 2 →
    orderOf (β * MulAut.conj ℓ) = 8 →
    ∃ M : Subgroup S, (∀ y ∈ M, β y = y) ∧ (∀ c : S, β c = c → ∀ y ∈ M, c * y * c⁻¹ ∈ M) ∧
      Nonempty (↥M ≃* alternatingGroup (Fin 6))

@[expose] def P1Models : Prop :=
  ∀ (S : Type) [Group S], (Blueprint.LieModel S .PSL 4 3 1 ∨ Blueprint.LieModel S .PSU 4 3 1) →
    P1ModelFacts S

end CFSG.ComponentClassification.HarrisLit.P1
