module

public import CFSG.CharacterTheory.Wreathed.ConditionalCentralPowerRegularBases

public noncomputable section

open scoped Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers

section Definitions

variable {E H : Type} [Group E] [Fintype E] [Group H]

@[expose] noncomputable def linearAugmentationLabels (basis : FiniteIrreducibleCharacterBasis E)
    (fE : E →* H) {m : ℕ} (ℓ : Fin m → H → ℂ) (Φ : H → ℂ) : Finset basis.index :=
  Finset.univ.filter fun l => ∃ r : Fin m,
    (basis.representation l).character = (fun y => ℓ r (fE y)) ∨
      (basis.representation l).character = (fun y => ℓ r (fE y) * Φ (fE y))

@[expose] noncomputable def principalSeriesLabels (basis : FiniteIrreducibleCharacterBasis E)
    (fE : E →* H) (PH : Set (H → ℂ)) : Finset basis.index :=
  Finset.univ.filter fun l => ∃ θ ∈ PH, (basis.representation l).character = fun y => θ (fE y)

@[expose] noncomputable def cuspidalLabels (basis : FiniteIrreducibleCharacterBasis E)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (principal : basis.index)
    (fE : E →* H) {m : ℕ} (ℓ : Fin m → H → ℂ) (Φ : H → ℂ) (PH : Set (H → ℂ)) :
    Finset basis.index :=
  coefficientBlock basis (localizedComplexIntegerRing ideal) principal \
    (linearAugmentationLabels basis fE ℓ Φ ∪ principalSeriesLabels basis fE PH)

structure ConditionalPrincipalSeriesCuspidalData (basis : FiniteIrreducibleCharacterBasis E)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (principal : basis.index)
    (fE : E →* H) {I : Type*} (Θ : I → H → ℂ) (adm sel : I → Prop) (PH : Set (H → ℂ)) {m : ℕ}
    (ℓ : Fin m → H → ℂ) (Φ : H → ℂ) (ε : ℤ) (q d κ : ℕ) : Prop where
  regular_basis : PrincipalRegularIntegralBasisData basis ideal principal (fun y => Φ (fE y)) ε q
    ((m : ℤ) • !![4, -2; -2, ((m / 2 + 1 : ℕ) : ℤ)])
  theta_irreducible : ∀ i, adm i → (fun y => Θ i (fE y)) ∈ BlocksIrr E
  theta_principal : ∀ i, adm i →
    ((∃ l ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation l).character = fun y => Θ i (fE y)) ↔ sel i)
  series_subset : principalSeriesLabels basis fE PH ⊆
    coefficientBlock basis (localizedComplexIntegerRing ideal) principal
  series_card : (principalSeriesLabels basis fE PH).card = m * (κ - 1) / 2
  series_odd : ∀ l ∈ principalSeriesLabels basis fE PH, ∀ y : E, Odd (orderOf y) →
    (basis.representation l).character y = 1 + Φ (fE y)
  series_row : ∀ l ∈ principalSeriesLabels basis fE PH,
    oddRestriction (basis.representation l).character =
      (1 - ε) • oddRestriction (1 : E → ℂ) +
        ε • oddRestriction (1 + (ε : ℂ) • fun y => Φ (fE y))
  cuspidal : ∃ u : cuspidalLabels basis ideal principal fE ℓ Φ PH → ℕ,
    (∀ χ, 0 < u χ ∧ u χ ∣ d ∧
      (basis.representation χ).character 1 = (u χ : ℂ) * ((q : ℂ) - 1) ∧
      (∀ y : E, Odd (orderOf y) →
        (basis.representation χ).character y = (u χ : ℂ) * (Φ (fE y) - 1)) ∧
      oddRestriction (basis.representation χ).character =
        (-(1 + ε) * (u χ : ℤ)) • oddRestriction (1 : E → ℂ) +
          (ε * (u χ : ℤ)) • oddRestriction (1 + (ε : ℂ) • fun y => Φ (fE y))) ∧
    (ε = 1 → ∑ χ, u χ ^ 2 = m / 2) ∧ (ε = -1 → ∑ χ, u χ ^ 2 = m * (m - 1) / 2)
  cuspidal_gram : ∀ Q : Matrix (cuspidalLabels basis ideal principal fE ℓ Φ PH) (Fin 2) ℤ,
    (∀ χ : cuspidalLabels basis ideal principal fE ℓ Φ PH,
      oddRestriction (basis.representation χ).character =
        Q χ 0 • oddRestriction (1 : E → ℂ) +
          Q χ 1 • oddRestriction (1 + (ε : ℂ) • fun y => Φ (fE y))) →
    (ε = 1 → Q.transpose * Q = ((m / 2 : ℕ) : ℤ) • !![4, -2; -2, 1]) ∧
      (ε = -1 → Q.transpose * Q = ((m * (m - 1) / 2 : ℕ) : ℤ) • !![0, 0; 0, 1])

end Definitions

@[expose] def PrincipalFamilyCorrespondence {E E' H : Type} [Group E] [Fintype E] [Group E']
    [Fintype E'] [Group H] (σ : E' →* E) (basis : FiniteIrreducibleCharacterBasis E)
    (basis' : FiniteIrreducibleCharacterBasis E') (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (principal : basis.index) (principal' : basis'.index) (fE : E →* H)
    (fE' : E' →* H) {m : ℕ} (ℓ : Fin m → H → ℂ) (Φ : H → ℂ) (PH : Set (H → ℂ)) (ε : ℤ) :
    Prop :=
  ∃ τ : coefficientBlock basis (localizedComplexIntegerRing ideal) principal ≃
      coefficientBlock basis' (localizedComplexIntegerRing ideal) principal',
    (∀ θ, (basis'.representation (τ θ)).character = (basis.representation θ).character ∘ σ) ∧
    (∀ (θ : coefficientBlock basis (localizedComplexIntegerRing ideal) principal) (r₀ r₁ : ℤ),
      oddRestriction (basis.representation θ).character =
          r₀ • oddRestriction (1 : E → ℂ) +
            r₁ • oddRestriction (1 + (ε : ℂ) • fun y => Φ (fE y)) ↔
        oddRestriction (basis'.representation (τ θ)).character =
          r₀ • oddRestriction (1 : E' → ℂ) +
            r₁ • oddRestriction (1 + (ε : ℂ) • fun y => Φ (fE' y))) ∧
    (∀ θ : coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      θ.1 ∈ linearAugmentationLabels basis fE ℓ Φ ↔
        (τ θ).1 ∈ linearAugmentationLabels basis' fE' ℓ Φ) ∧
    (∀ θ : coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      θ.1 ∈ principalSeriesLabels basis fE PH ↔ (τ θ).1 ∈ principalSeriesLabels basis' fE' PH) ∧
    ∀ θ : coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      θ.1 ∈ cuspidalLabels basis ideal principal fE ℓ Φ PH ↔
        (τ θ).1 ∈ cuspidalLabels basis' ideal principal' fE' ℓ Φ PH

end CFSG.Wreathed
