module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15RVertexExclG2

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Open (IsElemAbelian classicalInvolutionOddCore)

section Cent

variable {p f : ℕ} [Fact p.Prime]

@[expose] def G2D4VertexExclCent (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (hΩ : HypOmegaMod p f Ω),
    (∀ M ∈ Ω, AEmpty Ω M) → ∀ c : G, IsPGroup 2 (Subgroup.zpowers c) →
      (∀ N ∈ tqMembers Ω c, N ≤ Subgroup.centralizer ({c} : Set G)) →
        ∀ (D : LocalLieSystemAt p f (exactFamily Ω c) c) (j : Fin D.card),
          (D.tag j = .G2 ∨ D.tag j = .trialityD4) →
            ∀ (M M' : Subgroup G) (b : G), M ∈ tqMembers Ω c → M' ∈ tqMembers Ω c →
              IsClassicalMember p f M b → IsClassicalMember p f M' b → M' ≠ M →
                modOdd c (exactCore c M) ≤
                  (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range →
                modOdd c (exactCore c M') ≤
                  (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range →
                  False

theorem g2d4VertexExclCent : G2D4VertexExclCent p f := by
  intro G _ _ Ω hΩ hA c hc2 hcent D j hj M M' b hM hM' hMb hM'b hne hMj hM'j
  have hf : 0 < f := by
    have h1 : 1 ≤ D.exp j := (D.admissible j).2.1
    rcases D.exp_eq j with h2 | ⟨-, h2⟩ <;> omega
  obtain ⟨hp, hq⟩ := params_of_isClassicalMember hMb hf
  rcases hj with hG2 | hD4
  · exact false_of_g2_twin_of_centralizing hp hq hΩ hA hc2 hcent D j hG2 hM hM' hMb hM'b hne hMj
      hM'j
  · exact false_of_trialityD4_sec hp hq hΩ hc2 D j hD4 hM hM' hMb hM'b hne hMj hM'j

end Cent

section Fuzzy

variable {p f : ℕ} [Fact p.Prime]

@[expose] def G2VertexExclFuzzy (p f : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (hΩ : HypOmegaMod p f Ω),
      (∀ M ∈ Ω, AEmpty Ω M) → ∀ c : G, IsPGroup 2 (Subgroup.zpowers c) →
        (∃ N ∈ tqMembers Ω c, ¬ N ≤ Subgroup.centralizer ({c} : Set G)) →
          ∀ (D : LocalLieSystemAt p f (exactFamily Ω c) c) (j : Fin D.card), D.tag j = .G2 →
            ∀ (M M' : Subgroup G) (b : G), M ∈ tqMembers Ω c → M' ∈ tqMembers Ω c →
              IsClassicalMember p f M b → IsClassicalMember p f M' b → M' ≠ M →
                modOdd c (exactCore c M) ≤
                  (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range →
                modOdd c (exactCore c M') ≤
                  (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range →
                  False

theorem g2VertexExcl_of_fuzzy (h : G2VertexExclFuzzy p f) : G2VertexExcl p f := by
  intro hp hq G _ _ Ω hΩ hA c hc2 D j hG2 M M' b hM hM' hMb hM'b hne hMj hM'j
  by_cases hcent : ∀ N ∈ tqMembers Ω c, N ≤ Subgroup.centralizer ({c} : Set G)
  · exact false_of_g2_twin_of_centralizing hp hq hΩ hA hc2 hcent D j hG2 hM hM' hMb hM'b hne hMj
      hM'j
  · push Not at hcent
    exact h hp hq G Ω hΩ hA c hc2 hcent D j hG2 M M' b hM hM' hMb hM'b hne hMj hM'j

theorem g2d4VertexExcl_of_fuzzy (h : G2VertexExclFuzzy p f) : G2D4VertexExcl p f :=
  g2d4VertexExcl_of_g2 (g2VertexExcl_of_fuzzy h)

end Fuzzy

end CFSG.ClassicalInvolution.Asc77
