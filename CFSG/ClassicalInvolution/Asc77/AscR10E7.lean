module

public import CFSG.ClassicalInvolution.Asc77.AscR10E5
public import CFSG.ClassicalInvolution.Asc77.AscR10D3b

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)
open scoped MatrixGroups commutatorElement



@[expose] def StdDich3Gen (p : ℕ) [Fact p.Prime] (t : StatedLieTag) (n e : ℕ) : Prop :=
  p ^ e = 3 →
    ∀ R₁ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D,
    ∀ R₂ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D,
    ∀ c₁ c₂ : (Generic.modelUniv t n p e Fact.out).K, c₁ ∈ R₁ → c₂ ∈ R₂ →
      orderOf c₁ = 2 → orderOf c₂ = 2 → c₁ * c₂ = c₂ * c₁ →
      R₁ = R₂ ∨ Commutes R₁ R₂ ∨
        (∃ W, LinearBlockStandardPair (GaloisField p e) W R₁ R₂) ∨
        ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₁ R₂

section Branches

variable {p : ℕ} [Fact p.Prime]

@[expose] def A2Branch3 (p : ℕ) [Fact p.Prime] (t : StatedLieTag) (n e : ℕ) : Prop :=
  p ^ e = 3 →
    ∀ R₁ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D,
    ∀ R₂ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D,
    ∀ c₁ c₂ : (Generic.modelUniv t n p e Fact.out).K, c₁ ∈ R₁ → c₂ ∈ R₂ →
      orderOf c₁ = 2 → orderOf c₂ = 2 → c₁ * c₂ = c₂ * c₁ →
      ¬ ((∀ r ∈ R₁, c₂ * r = r * c₂) ∧ ∀ r ∈ R₂, c₁ * r = r * c₁) →
      (∃ W, LinearBlockStandardPair (GaloisField p e) W R₁ R₂) ∨
        ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₁ R₂

@[expose] def A2BranchLeft3 (p : ℕ) [Fact p.Prime] (t : StatedLieTag) (n e : ℕ) : Prop :=
  p ^ e = 3 →
    ∀ R₁ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D,
    ∀ R₂ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D,
    ∀ c₁ c₂ : (Generic.modelUniv t n p e Fact.out).K, c₁ ∈ R₁ → c₂ ∈ R₂ →
      orderOf c₁ = 2 → orderOf c₂ = 2 → c₁ * c₂ = c₂ * c₁ →
      ¬ (∀ r ∈ R₁, c₂ * r = r * c₂) →
      (∃ W, LinearBlockStandardPair (GaloisField p e) W R₁ R₂) ∨
        ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₁ R₂

theorem A2BranchLeft3.a2Branch3 {t : StatedLieTag} {n e : ℕ} (h : A2BranchLeft3 p t n e) :
    A2Branch3 p t n e := by
  intro h3 R₁ h₁ R₂ h₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ hcomm hn
  by_cases h₂₁ : ∀ r ∈ R₁, c₂ * r = r * c₂
  · have h₁₂ : ¬ ∀ r ∈ R₂, c₁ * r = r * c₁ := fun h' => hn ⟨h₂₁, h'⟩
    rcases h h3 R₂ h₂ R₁ h₁ c₂ c₁ hc₂ hc₁ ho₂ ho₁ hcomm.symm h₁₂ with ⟨W, hW⟩ | ⟨W, hW⟩
    · exact Or.inl ⟨W, linearBlockStandardPair_symm hW⟩
    · exact Or.inr ⟨W, unitaryBlockStandardPair_symm hW⟩
  · exact h h3 R₁ h₁ R₂ h₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ hcomm h₂₁

theorem stdDich3Gen_of_branches {t : StatedLieTag} {n e : ℕ} (hO : OrthBranch3 p t n e)
    (hA : A2Branch3 p t n e) : StdDich3Gen p t n e := by
  intro h3 R₁ h₁ R₂ h₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ hcomm
  by_cases h : (∀ r ∈ R₁, c₂ * r = r * c₂) ∧ ∀ r ∈ R₂, c₁ * r = r * c₁
  · rcases hO h3 R₁ h₁ R₂ h₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ h.1 h.2 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases hA h3 R₁ h₁ R₂ h₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ hcomm h with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

end Branches

theorem stdDich3_of_gen {t : StatedLieTag} {n : ℕ}
    (h : StdDich3Gen 3 t n 1) : CFSG.ClassicalInvolution.Asc77.T3CII.StdDich3 t n :=
  fun R₁ h₁ R₂ h₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ hcomm =>
    h (by norm_num) R₁ h₁ R₂ h₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ hcomm

end CFSG.ClassicalInvolution.ModelFacts
