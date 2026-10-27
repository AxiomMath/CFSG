module

public import CFSG.RankThree.PartOne.KF.UnitaryDiag
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwLineDefs
public import CFSG.LieType.Seitz.Defs
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KFU

set_option linter.unusedSectionVars false

section Layer


@[expose] def TwLayerAct (K : Type) [Field K] (σ : K ≃+* K) (h₀ : ModGL TwistTag.E6.tag K)
    (L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K)) {ℓ f : ℕ} (h : UnitaryFieldData ℓ f K)
    (ρ : Fin 3 → unitarySU ℓ f K 3 →* twistedE6RootGroup K σ) : Prop :=
  (∀ i, Function.Injective (ρ i)) ∧
  (∀ i, (ρ i).range.map (twistedE6RootGroup K σ).subtype = L i) ∧
  ∀ s : twistedE6RootGroup K σ, (s : ModGL TwistTag.E6.tag K) = h₀ →
    ∀ ε ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ, ε * MulAut.conj s = MulAut.conj s * ε →
      (∀ i, (ρ i).range.map ε.toMonoidHom = (ρ i).range) →
      ∀ i, ∃ γ : primeFormUnitary h (idGram K 3), ∀ x, ε (ρ i x) = ρ i (conjSU h γ x)

@[expose] def TwLayerModel : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 → 3 ∣ q + 1 → q ≠ 2 →
    ∀ (h₀ : ModGL TwistTag.E6.tag K) (L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K))
      (T : Subgroup (ModGL TwistTag.E6.tag K)) (n : ModGL TwistTag.E6.tag K),
      TwE6ThreeA2Line K σ h₀ L T n →
      ∃ (ℓ f : ℕ) (h : UnitaryFieldData ℓ f K)
        (ρ : Fin 3 → unitarySU ℓ f K 3 →* twistedE6RootGroup K σ),
        ℓ ^ f = q ∧ TwLayerAct K σ h₀ L h ρ

end Layer

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
