module

public import CFSG.RankThree.PartTwo.KFacts.AutPSU
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwLayerStep

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartTwo.KFacts CFSG.LieType.SeitzGeneration

@[expose] def TwFixedNonCentral : Prop :=
  ∀ (ℓ f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData ℓ f K), 3 ∣ ℓ ^ f + 1 → ℓ ^ f ≠ 2 →
    ∀ γ : unitaryIsom3 h, suConj h γ ^ 3 = 1 →
      ∃ k : unitarySU ℓ f K 3, k ∉ Subgroup.center (unitarySU ℓ f K 3) ∧ suConj h γ k = k

@[expose] def TwToralPlane : Prop :=
  ∀ (ℓ f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData ℓ f K), 3 ∣ ℓ ^ f + 1 → ℓ ^ f ≠ 2 →
    ∀ γ₁ γ₂ : unitaryIsom3 h, γ₁ * γ₂ = γ₂ * γ₁ → suConj h γ₁ ^ 3 = 1 → suConj h γ₂ ^ 3 = 1 →
      (∀ i j : ℕ, suConj h γ₁ ^ i * suConj h γ₂ ^ j = 1 → 3 ∣ i ∧ 3 ∣ j) →
      PlaneGen (Subgroup.closure ({suConj h γ₁, suConj h γ₂} :
        Set (MulAut (unitarySU ℓ f K 3))))

@[expose] def TwInnerHeisPlane : Prop :=
  ∀ (ℓ f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData ℓ f K), 3 ∣ ℓ ^ f + 1 → ℓ ^ f ≠ 2 →
    ∀ γ₁ γ₂ : unitaryIsom3 h, γ₁ * γ₂ ≠ γ₂ * γ₁ →
      suConj h γ₁ * suConj h γ₂ = suConj h γ₂ * suConj h γ₁ →
      suConj h γ₁ ^ 3 = 1 → suConj h γ₂ ^ 3 = 1 →
      (∀ i j : ℕ, suConj h γ₁ ^ i * suConj h γ₂ ^ j = 1 → 3 ∣ i ∧ 3 ∣ j) →
      Subgroup.closure ({suConj h γ₁, suConj h γ₂} : Set (MulAut (unitarySU ℓ f K 3))) ≤
        (MulAut.conj : unitarySU ℓ f K 3 →* MulAut (unitarySU ℓ f K 3)).range →
      PlaneGen (Subgroup.closure ({suConj h γ₁, suConj h γ₂} :
        Set (MulAut (unitarySU ℓ f K 3))))

@[expose] def TwOuterHeisPlane : Prop :=
  ∀ (ℓ f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData ℓ f K), 3 ∣ ℓ ^ f + 1 → ℓ ^ f ≠ 2 →
    ∀ γ₁ γ₂ : unitaryIsom3 h, γ₁ * γ₂ ≠ γ₂ * γ₁ →
      suConj h γ₁ * suConj h γ₂ = suConj h γ₂ * suConj h γ₁ →
      suConj h γ₁ ^ 3 = 1 → suConj h γ₂ ^ 3 = 1 →
      (∀ i j : ℕ, suConj h γ₁ ^ i * suConj h γ₂ ^ j = 1 → 3 ∣ i ∧ 3 ∣ j) →
      ¬ Subgroup.closure ({suConj h γ₁, suConj h γ₂} : Set (MulAut (unitarySU ℓ f K 3))) ≤
        (MulAut.conj : unitarySU ℓ f K 3 →* MulAut (unitarySU ℓ f K 3)).range →
      PlaneGen (Subgroup.closure ({suConj h γ₁, suConj h γ₂} :
        Set (MulAut (unitarySU ℓ f K 3))))

theorem twPlaneGen_of_stmts (hT : TwToralPlane) (hI : TwInnerHeisPlane) (hO : TwOuterHeisPlane)
    {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) (hq3 : 3 ∣ ℓ ^ f + 1)
    (hq : ℓ ^ f ≠ 2) :
    ∀ a₁ ∈ (suConj h).range, ∀ a₂ ∈ (suConj h).range, a₁ * a₂ = a₂ * a₁ → a₁ ^ 3 = 1 →
      a₂ ^ 3 = 1 → (∀ i j : ℕ, a₁ ^ i * a₂ ^ j = 1 → 3 ∣ i ∧ 3 ∣ j) →
        PlaneGen (Subgroup.closure ({a₁, a₂} : Set (MulAut (unitarySU ℓ f K 3)))) := by
  rintro _ ⟨γ₁, rfl⟩ _ ⟨γ₂, rfl⟩ hc h1 h2 hind
  by_cases hlift : γ₁ * γ₂ = γ₂ * γ₁
  · exact hT ℓ f K h hq3 hq γ₁ γ₂ hlift h1 h2 hind
  · by_cases hin : Subgroup.closure ({suConj h γ₁, suConj h γ₂} :
        Set (MulAut (unitarySU ℓ f K 3))) ≤
        (MulAut.conj : unitarySU ℓ f K 3 →* MulAut (unitarySU ℓ f K 3)).range
    · exact hI ℓ f K h hq3 hq γ₁ γ₂ hlift hc h1 h2 hind hin
    · exact hO ℓ f K h hq3 hq γ₁ γ₂ hlift hc h1 h2 hind hin

theorem twLayerFacts_of_stmts (hNC : TwFixedNonCentral) (hT : TwToralPlane)
    (hI : TwInnerHeisPlane) (hO : TwOuterHeisPlane) {ℓ f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hq3 : 3 ∣ ℓ ^ f + 1) (hq : ℓ ^ f ≠ 2)
    (hnab : ∃ x y : unitarySU ℓ f K 3, x * y ≠ y * x)
    (hnorm : ∀ N : Subgroup (unitarySU ℓ f K 3), N.Normal →
      N ≤ Subgroup.center (unitarySU ℓ f K 3) ∨ N = ⊤) :
    TwLayerFacts (unitarySU ℓ f K 3) (suConj h).range where
  nonabelian := hnab
  normal := hnorm
  plane := twPlaneGen_of_stmts hT hI hO h hq3 hq
  fixed := by
    rintro _ ⟨γ, rfl⟩ ha
    exact hNC ℓ f K h hq3 hq γ ha

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
