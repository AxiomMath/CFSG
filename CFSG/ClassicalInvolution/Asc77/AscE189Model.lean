module

public import CFSG.ClassicalInvolution.Asc77.WP1Defs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped commutatorElement

abbrev ModelGrp (p e : ℕ) [Fact p.Prime] (t : StatedLieTag) (n : ℕ) : Type :=
  (modelUniv t n p e Fact.out).K

abbrev modelFund (p e : ℕ) [Fact p.Prime] (t : StatedLieTag) (n : ℕ) :
    Set (Subgroup (ModelGrp p e t n)) :=
  fundamentalSubgroups t (modelUniv t n p e Fact.out).D

@[expose] def E189AtFam (K : Type) [Group K] (𝓕 : Set (Subgroup K)) : Prop :=
  ∀ N : Subgroup K, N ≤ Subgroup.center K →
    ∀ F₁ ∈ 𝓕, ∀ z₁ : K, IsUniqueInvolution F₁ z₁ →
      ∀ g : K, ⁅z₁, g * z₁ * g⁻¹⁆ ∈ N → z₁ * (g * z₁ * g⁻¹) ∉ N →
        conjSub (g * z₁ * g⁻¹) F₁ ≠ F₁ → Commutes F₁ (conjSub (g * z₁ * g⁻¹) F₁) →
          (∀ S : Subgroup K, (∃ y, S = conjSub y F₁) →
            ((S = F₁ ∨ Commutes S F₁) ↔
              (S = conjSub (g * z₁ * g⁻¹) F₁ ∨ Commutes S (conjSub (g * z₁ * g⁻¹) F₁)))) →
          (∃ F₃ ∈ 𝓕, F₃ ≠ F₁ ∧ Commutes F₁ F₃ ∧ (∃ y, F₃ = conjSub y F₁) ∧
              ∃ z₃, IsUniqueInvolution F₃ z₃ ∧ z₁⁻¹ * z₃ ∈ N ∧
                ∃ R₁ R₃ : Subgroup K, IsSylow2In R₁ F₁ ∧ IsSylow2In R₃ F₃ ∧
                ∃ u x : K, u ∈ R₁ ⊔ R₃ ∧ u ∉ N ∧ u * u ∈ N ∧
                  (x * u * x⁻¹)⁻¹ * (z₁ * (g * z₁ * g⁻¹)) ∈ N) ∨
          (∃ x : K, ∃ M₂ ∈ 𝓕, M₂ ≠ conjSub x F₁ ∧
              Commutes (conjSub x F₁) M₂ ∧ (∃ y, M₂ = conjSub y F₁) ∧
              ∃ z₂, IsUniqueInvolution M₂ z₂ ∧ (x * z₁ * x⁻¹)⁻¹ * z₂ ∈ N ∧
                ∀ w ∈ conjSub x F₁ ⊔ M₂, ⁅w, z₁ * (g * z₁ * g⁻¹)⁆ ∈ N)

@[expose] def E189ModelAt (p e : ℕ) [Fact p.Prime] (t : StatedLieTag) (n : ℕ) : Prop :=
  E189AtFam (ModelGrp p e t n) (modelFund p e t n)

@[expose] def E189Model (p f : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → ∀ (t : StatedLieTag) (n e : ℕ), IsFundTag t → StatedLieAdmissible t n p e →
    (e = f ∨ (t = .trialityD4 ∧ 3 * e = f)) → E189ModelAt p e t n

end CFSG.ClassicalInvolution.Asc77
