module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwLayerDefs

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KFU

set_option linter.unusedSectionVars false

section Torus


@[expose] def twLayerProd {K : Type} [Field K] {σ : K ≃+* K} {ℓ f : ℕ}
    (ρ : Fin 3 → unitarySU ℓ f K 3 →* twistedE6RootGroup K σ)
    (x : Fin 3 → unitarySU ℓ f K 3) : ModGL TwistTag.E6.tag K :=
  ((ρ 0 (x 0) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) *
    ((ρ 1 (x 1) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) *
    ((ρ 2 (x 2) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K)

@[expose] def TwTorusAct (K : Type) [Field K] (σ : K ≃+* K) (h₀ : ModGL TwistTag.E6.tag K)
    (T : Subgroup (ModGL TwistTag.E6.tag K)) {ℓ f : ℕ} (h : UnitaryFieldData ℓ f K)
    (ρ : Fin 3 → unitarySU ℓ f K 3 →* twistedE6RootGroup K σ) : Prop :=
  ∃ (Th : Subgroup (ModGL TwistTag.E6.tag K))
    (A : Fin 3 → ModGL TwistTag.E6.tag K → primeFormUnitary h (idGram K 3)),
    T ≤ Th ∧ (∀ x ∈ Th, ∀ y ∈ Th, x * y = y * x) ∧
    (∀ i, ∀ τ ∈ Th, ∀ τ' ∈ Th, A i τ * A i τ' = A i τ' * A i τ) ∧
    (∀ i, ∀ τ ∈ Th, ∀ w : unitarySU ℓ f K 3,
      τ * ((ρ i w : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * τ⁻¹ =
        ((ρ i (conjSU h (A i τ) w) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K)) ∧
    ∀ s : twistedE6RootGroup K σ, (s : ModGL TwistTag.E6.tag K) = h₀ →
      ∀ ε ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ, ε * MulAut.conj s = MulAut.conj s * ε →
        (∀ i, (ρ i).range.map ε.toMonoidHom = (ρ i).range) →
        ∃ τ ∈ Th, ∃ x : Fin 3 → unitarySU ℓ f K 3, ∀ c : twistedE6RootGroup K σ,
          ((ε c : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
            (τ * twLayerProd ρ x) * (c : ModGL TwistTag.E6.tag K) * (τ * twLayerProd ρ x)⁻¹

@[expose] def TwTorusModel : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 → 3 ∣ q + 1 → q ≠ 2 →
    ∀ (h₀ : ModGL TwistTag.E6.tag K) (L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K))
      (T : Subgroup (ModGL TwistTag.E6.tag K)) (n : ModGL TwistTag.E6.tag K),
      TwE6ThreeA2Line K σ h₀ L T n →
      ∃ (ℓ f : ℕ) (h : UnitaryFieldData ℓ f K)
        (ρ : Fin 3 → unitarySU ℓ f K 3 →* twistedE6RootGroup K σ),
        ℓ ^ f = q ∧ TwLayerAct K σ h₀ L h ρ ∧ TwTorusAct K σ h₀ T h ρ

theorem twLayerModel_of_torusModel (hm : TwTorusModel) : TwLayerModel :=
  fun K _ _ σ q h1 h2 h3 h4 h5 h₀ L T n hl => by
    obtain ⟨ℓ, f, h, ρ, hq, hact, -⟩ := hm K σ q h1 h2 h3 h4 h5 h₀ L T n hl
    exact ⟨ℓ, f, h, ρ, hq, hact⟩

end Torus

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
