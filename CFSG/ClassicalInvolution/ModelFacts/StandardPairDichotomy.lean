module

public import CFSG.ClassicalInvolution.Balance.QNineStandard

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models.Transfer
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)
open scoped commutatorElement

section Longest

variable {K : Type} [Group K]

@[expose] def longestFundamental (D : UniversalRootDatum K) : Set (Subgroup K) :=
  {R | ∃ (g : K) (γ : Fin D.rank → ℤ), Generic.IsLongestRoot D γ ∧
    R = (D.rootGroup γ ⊔ D.rootGroup (-γ)).map (MulAut.conj g).toMonoidHom}

theorem longestFundamental_subset (t : StatedLieTag) (D : UniversalRootDatum K) :
    longestFundamental D ⊆ Generic.fundamentalSubgroups t D := by
  rintro R ⟨g, γ, hγ, rfl⟩
  exact ⟨g, γ, Or.inl hγ, rfl⟩

theorem fundamentalSubgroups_subset_longest {t : StatedLieTag} (ht₁ : t ≠ .G2)
    (ht₂ : t ≠ .trialityD4) (D : UniversalRootDatum K) :
    Generic.fundamentalSubgroups t D ⊆ longestFundamental D := by
  rintro R ⟨g, γ, hγ, rfl⟩
  rcases hγ with h | ⟨h, -⟩ | ⟨h, -⟩
  · exact ⟨g, γ, h, rfl⟩
  · exact absurd h ht₁
  · exact absurd h ht₂

end Longest

@[expose] def StandardPairDichotomy (p : ℕ) [Fact p.Prime] (t : StatedLieTag) (n e : ℕ) : Prop :=
  p ≠ 2 → 5 ≤ p ^ e →
    ∀ R₁ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D,
    ∀ R₂ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D,
    ∀ c₁ c₂ : (Generic.modelUniv t n p e Fact.out).K, c₁ ∈ R₁ → c₂ ∈ R₂ →
      orderOf c₁ = 2 → orderOf c₂ = 2 → c₁ * c₂ = c₂ * c₁ →
      R₁ = R₂ ∨ Commutes R₁ R₂ ∨
        (∃ W, LinearBlockStandardPair (GaloisField p e) W R₁ R₂) ∨
        ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₁ R₂

@[expose] def StandardPairDichotomyFacts (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (t : StatedLieTag) (n e : ℕ), Generic.IsFundTag t → StatedLieAdmissible t n p e →
    StandardPairDichotomy p t n e

section Map

variable {p : ℕ} [Fact p.Prime] {t : StatedLieTag} {n e : ℕ}

theorem StandardPairDichotomy.map_of_commute (h : StandardPairDichotomy p t n e) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ e) {X : Type} [Group X] (ψ : (Generic.modelUniv t n p e Fact.out).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (Generic.modelUniv t n p e Fact.out).K)
    {R₁ R₂ : Subgroup (Generic.modelUniv t n p e Fact.out).K}
    (h₁ : R₁ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D)
    (h₂ : R₂ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D)
    {c₁ c₂ : (Generic.modelUniv t n p e Fact.out).K} (hc₁ : c₁ ∈ R₁) (hc₂ : c₂ ∈ R₂)
    (ho₁ : orderOf c₁ = 2) (ho₂ : orderOf c₂ = 2) (hcomm : c₁ * c₂ = c₂ * c₁) :
    R₁.map ψ = R₂.map ψ ∨ Commutes (R₁.map ψ) (R₂.map ψ) ∨
      (∃ W, LinearBlockStandardPair (GaloisField p e) W (R₁.map ψ) (R₂.map ψ)) ∨
      ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W (R₁.map ψ) (R₂.map ψ) := by
  have hf : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · simp at hq
    · exact h
  rcases h hp2 hq R₁ h₁ R₂ h₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ hcomm with rfl | hcm | hl | hu
  · exact Or.inl rfl
  · refine Or.inr (Or.inl ?_)
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcm x hx y hy]
  · obtain ⟨W, hW⟩ := hl
    exact Or.inr (Or.inr (Or.inl
      ⟨_, Balance.linearBlockStandardPair_map_of_ker_le_center hW ψ hker⟩))
  · obtain ⟨W, hW⟩ := hu
    exact Or.inr (Or.inr (Or.inr ⟨_,
      Balance.unitaryBlockStandardPair_map_of_ker_le_center (K₀ := GaloisField p (2 * e))
        (card_galoisField_two_mul p e hf) hq hW ψ hker⟩))

theorem StandardPairDichotomy.map (h : StandardPairDichotomy p t n e) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ e) {X : Type} [Group X] (ψ : (Generic.modelUniv t n p e Fact.out).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (Generic.modelUniv t n p e Fact.out).K)
    (hinv : KerInvolutionFree ψ)
    {R₁ R₂ : Subgroup (Generic.modelUniv t n p e Fact.out).K}
    (h₁ : R₁ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D)
    (h₂ : R₂ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D)
    {c₁ c₂ : (Generic.modelUniv t n p e Fact.out).K} (hc₁ : c₁ ∈ R₁) (hc₂ : c₂ ∈ R₂)
    (ho₁ : orderOf c₁ = 2) (ho₂ : orderOf c₂ = 2) (hc : ψ c₁ * ψ c₂ = ψ c₂ * ψ c₁) :
    R₁.map ψ = R₂.map ψ ∨ Commutes (R₁.map ψ) (R₂.map ψ) ∨
      (∃ W, LinearBlockStandardPair (GaloisField p e) W (R₁.map ψ) (R₂.map ψ)) ∨
      ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W (R₁.map ψ) (R₂.map ψ) := by
  have hsq₂ : c₂ * c₂ = 1 := by rw [← pow_two]; exact ho₂ ▸ pow_orderOf_eq_one c₂
  have hcomm : c₁ * c₂ = c₂ * c₁ := by
    have hκ : ⁅c₁, c₂⁆ ∈ ψ.ker := commutator_mem_ker ψ hc
    refine commutatorElement_eq_one_iff_mul_comm.mp (hinv _ hκ ?_)
    refine sq_eq_one_of_conj_eq (g := c₁) (i := c₂) hsq₂ (hker hκ) ?_
    rw [commutatorElement_def]
    group
  exact h.map_of_commute hp2 hq ψ hker h₁ h₂ hc₁ hc₂ ho₁ ho₂ hcomm

end Map

end CFSG.ClassicalInvolution.ModelFacts
