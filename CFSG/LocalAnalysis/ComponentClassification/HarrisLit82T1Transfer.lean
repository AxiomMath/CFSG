module

public import CFSG.GH74.GLS.Bg.Local.Transfer1515

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open Subgroup CFSG.GH74.GLS.Bg.Thompson

variable {X : Type} [Group X] [Finite X]

theorem conj_into_of_transfer [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    {S V : Subgroup X} (hS : IsPGroup 2 ↥S) (hSidx : ¬ 2 ∣ S.index)
    (hVn : ∀ t ∈ S, ∀ q ∈ V, t * q * t⁻¹ ∈ V)
    (hcyc : ∃ b ∈ S, ∀ t ∈ S, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ V)
    {x : X} (hxS : x ∈ S) (hxV : x ∉ V)
    (hb : ∀ (g : X) (k : ℕ), g⁻¹ * x ^ (2 * k) * g ∈ S → g⁻¹ * x ^ (2 * k) * g ∈ V)
    (hc : ∀ g : X, g⁻¹ * x * g ∈ S → IsExtremalIn 2 S (g⁻¹ * x * g) →
      g⁻¹ * x * g ∈ V ∨ x⁻¹ * (g⁻¹ * x * g) ∈ V) :
    ∃ g : X, g⁻¹ * x * g ∈ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases thompson_transfer_1515 hS hSidx hVn hcyc hxS hxV hb hc with
    ⟨N, hN, hNcyc, -, hxN⟩ | ⟨g, hg, -⟩
  · exfalso
    rcases hN.eq_bot_or_eq_top with rfl | rfl
    ·
      have : IsCyclic (X ⧸ (⊥ : Subgroup X)) := hNcyc
      have : IsCyclic X := isCyclic_of_surjective
        (QuotientGroup.quotientBot (G := X)).toMonoidHom (MulEquiv.surjective _)
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab (IsCyclic.commGroup.mul_comm a b)
    · exact hxN (mem_top x)
  · exact ⟨g, hg⟩

end CFSG.ComponentClassification.HarrisLit.T1
