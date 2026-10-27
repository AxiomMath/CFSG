module

public import CFSG.Goldschmidt75.TheoremBb
public import CFSG.Goldschmidt75.TheoremBc

public section

namespace CFSG.Goldschmidt75

open CFSG.Open Subgroup
open scoped Pointwise

universe u

theorem theoremB {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    {S : Subgroup G} (hSP : S ≤ P) (hS : fusionStronglyClosed (S : Set G) P) :
    (∀ U₁ U₂ : Set G, U₁ ⊆ P → U₂ ⊆ P → ∀ g : G, (fun x => g⁻¹ * x * g) '' U₁ = U₂ →
      ∃ n ∈ normalizer (S : Set G),
        (fun x => n⁻¹ * x * n) '' ((S : Set G) * U₁) = (S : Set G) * U₂) ∧
    (commutator G ⊓ P) ⊔ S =
      (⁅normalizer (S : Set G), normalizer (S : Set G)⁆ ⊓ P) ⊔ S ∧
    fusionStronglyClosed
      ((⁅centralizer (S : Set G), centralizer (S : Set G)⁆ ⊓ P : Subgroup G) : Set G) P :=
  ⟨fun _ _ hU₁ hU₂ _ hg => theoremB_a P hSP hS hU₁ hU₂ hg, theoremB_b P hSP hS,
    theoremB_c P hSP hS⟩

end CFSG.Goldschmidt75
