module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.FixPlaneStd
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter

open Matrix Subgroup CFSG.Open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.LieType.SeitzGeneration
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter

theorem fixPlaneGen_matrixProjectiveDerived {K : Type} [Field K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hQ : ∀ σ : K ≃+* K, orderOf σ = p → ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v))
    (hdesc : ∀ α : MulAut (matrixProjectiveDerived Q), IsOuterOfOrder p α →
      ∃ D ∈ (linearConjugationHom Q).range, ∃ (σ : K ≃+* K) (h : orderOf σ = p),
        α = D * fieldAutT Q σ (hQ σ h) * D⁻¹)
    (hplanes : ∀ (σ : K ≃+* K) (h : orderOf σ = p),
      ∀ A : Subgroup (matrixProjectiveDerived Q), A ≤ fixedSubgroup (fieldAutT Q σ (hQ σ h)) →
        IsElemAbelian p A → Nat.card A = p ^ 2 →
          fixedSubgroup (fieldAutT Q σ (hQ σ h)) ≤ Subgroup.closure
            {k | k ∈ fixedSubgroup (fieldAutT Q σ (hQ σ h)) ∧ ∃ b ∈ A, b ≠ 1 ∧ k * b = b * k}) :
    FixPlaneGen (matrixProjectiveDerived Q) p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hdesc' : ∀ α : MulAut (matrixProjectiveDerived Q), IsOuterOfOrder p α →
      ∃ D ∈ (linearConjugationHom Q).range,
        ∃ g ∈ {g | ∃ (σ : K ≃+* K) (h : orderOf σ = p), g = fieldAutT Q σ (hQ σ h)},
          α = D * g * D⁻¹ := by
    intro α hα
    obtain ⟨D, hD, σ, h, rfl⟩ := hdesc α hα
    exact ⟨D, hD, _, ⟨σ, h, rfl⟩, rfl⟩
  by_cases hex : ∃ σ0 : K ≃+* K, orderOf σ0 = p
  · obtain ⟨σ0, hσ0⟩ := hex
    refine fixPlaneGen_of_standard (linearConjugationHom Q).range
      {g | ∃ (σ : K ≃+* K) (h : orderOf σ = p), g = fieldAutT Q σ (hQ σ h)} hdesc'
      (fixedSubgroup (fieldAutT Q σ0 (hQ σ0 hσ0))) ?_ ?_
    · rintro _ ⟨σ₂, h₂, rfl⟩
      have hz : ∀ {τ₁ τ₂ : K ≃+* K}, orderOf τ₁ = p → orderOf τ₂ = p →
          τ₂ ∈ Subgroup.zpowers τ₁ := fun {τ₁ τ₂} g₁ g₂ => by
        have := zpowers_ringEquiv_eq_of_orderOf hℓ hf hK g₁ g₂
        exact this ▸ Subgroup.mem_zpowers τ₂
      have hmem : ∀ {τ₁ τ₂ : K ≃+* K} (g₁ : orderOf τ₁ = p) (g₂ : orderOf τ₂ = p),
          fieldPair Q τ₂ (hQ τ₂ g₂) ∈ Subgroup.zpowers (fieldPair Q τ₁ (hQ τ₁ g₁)) := by
        intro τ₁ τ₂ g₁ g₂
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hz g₁ g₂)
        refine Subgroup.mem_zpowers_iff.mpr ⟨m, Subtype.ext ?_⟩
        rw [fieldPair_zpow_val, hm]
        rfl
      exact fixedSubgroup_eq_of_zpowers_eq (matrixProjectiveConjugationHom Q)
        (le_antisymm ((Subgroup.zpowers_le).2 (hmem hσ0 h₂)) ((Subgroup.zpowers_le).2 (hmem h₂ hσ0)))
    · intro A hA hAa hAc
      exact hplanes σ0 hσ0 A hA hAa hAc
  · refine fixPlaneGen_of_standard (linearConjugationHom Q).range
      {g | ∃ (σ : K ≃+* K) (h : orderOf σ = p), g = fieldAutT Q σ (hQ σ h)} hdesc' ⊥ ?_ ?_
    · rintro _ ⟨σ, h, rfl⟩
      exact absurd ⟨σ, h⟩ hex
    · intro A hA _ _
      exact bot_le

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter
