module

public import CFSG.ClassicalInvolution.Balance.Theorem5Fuzzy
public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyPair
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.ClassicalInvolution.Balance.Theorem5
  (FuzzyFrameOn fuzzyFrames MemberClass FuzzyFrameBalance)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem rankThreeBalance_of_fuzzyFrameOn_pair [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hBelow : CITBelowU p f (Nat.card G)) {Ω : Set (Subgroup G)} {A : Subgroup G}
    (hA : FuzzyFrameOn p f Ω A)
    (hI : ∀ (J₁ J₂ J₃ : Subgroup G) (z₁ z₂ z₃ : G), J₁ ∈ Ω → J₂ ∈ Ω → J₃ ∈ Ω →
      AxisTriangle p f J₁ J₂ J₃ z₁ z₂ z₃ → triangleAxis z₁ z₂ z₃ = A →
        ∀ b ∈ A, b ≠ 1 → FuzzyPairInputs p f (triangleSecFamily J₁ J₂ J₃ b) b) :
    RankThreeBalance A := by
  obtain ⟨J₁, J₂, J₃, z₁, z₂, z₃, h1, h2, h3, hT, hne12, hne13, hne23, hind, hax⟩ :=
    hA.exists_axisTriangle
  have hB := hT.rankThreeBalance_pair hnab hp2 hq ModelFacts.modelClauseZero fundamentalWholeA1
    hBelow hne12 hne13 hne23 hind fun b hb hb1 =>
      hI J₁ J₂ J₃ z₁ z₂ z₃ h1 h2 h3 hT hax b (hax ▸ hb) hb1
  rwa [hax] at hB

@[expose] def FuzzyPairModelInputs (p f : ℕ) [Fact p.Prime] (𝒞 : MemberClass) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z → CITBelowU p f (Nat.card G) →
      RouteD.DeltaConnected (CoreAssembly.conjClass K) →
        CoreAssembly.IndepTriple p f (CoreAssembly.conjClass K) →
        ∀ (J₁ J₂ J₃ : Subgroup G) (z₁ z₂ z₃ : G), J₁ ∈ 𝒞 K → J₂ ∈ 𝒞 K → J₃ ∈ 𝒞 K →
          AxisTriangle p f J₁ J₂ J₃ z₁ z₂ z₃ → ∀ b ∈ triangleAxis z₁ z₂ z₃, b ≠ 1 →
            FuzzyPairInputs p f (triangleSecFamily J₁ J₂ J₃ b) b

theorem fuzzyFrameBalance_of_pairModelInputs {𝒞 : MemberClass}
    (hin : FuzzyPairModelInputs p f 𝒞) : FuzzyFrameBalance p f 𝒞 := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind A hA
  exact rankThreeBalance_of_fuzzyFrameOn_pair hnab hp2 hq hBelow hA
    fun J₁ J₂ J₃ z₁ z₂ z₃ h1 h2 h3 hT hax b hb hb1 =>
      hin G hnab hp2 hq K z hz hBelow hconn hind J₁ J₂ J₃ z₁ z₂ z₃ h1 h2 h3 hT b (hax ▸ hb) hb1

@[expose] def FuzzyNoF3 (p f : ℕ) [Fact p.Prime] (𝒞 : MemberClass) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z → CITBelowU p f (Nat.card G) →
      RouteD.DeltaConnected (CoreAssembly.conjClass K) →
        CoreAssembly.IndepTriple p f (CoreAssembly.conjClass K) →
        ∀ (J₁ J₂ J₃ : Subgroup G) (z₁ z₂ z₃ : G), J₁ ∈ 𝒞 K → J₂ ∈ 𝒞 K → J₃ ∈ 𝒞 K →
          AxisTriangle p f J₁ J₂ J₃ z₁ z₂ z₃ → ∀ b ∈ triangleAxis z₁ z₂ z₃, b ≠ 1 →
            NoComponentOverF3 p f (triangleSecFamily J₁ J₂ J₃ b) b

theorem FuzzyNoF3.of_ne_27 (𝒞 : MemberClass) (h27 : p ^ f ≠ 27) : FuzzyNoF3 p f 𝒞 := by
  intro G _ _ _ _ _ hq K z hz hBelow hconn hind J₁ J₂ J₃ z₁ z₂ z₃ h1 h2 h3 hT b hb hb1
  exact NoComponentOverF3.of_ne_27 b hq h27

theorem fuzzyPairModelInputs_of_layerGenerationPair {𝒞 : MemberClass}
    (hpair : LayerGenerationPair) (hF3 : FuzzyNoF3 p f 𝒞) : FuzzyPairModelInputs p f 𝒞 := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind J₁ J₂ J₃ z₁ z₂ z₃ h1 h2 h3 hT b hb hb1
  exact FuzzyPairInputs.of_facts hp2 hq
    (hF3 G hnab hp2 hq K z hz hBelow hconn hind J₁ J₂ J₃ z₁ z₂ z₃ h1 h2 h3 hT b hb hb1) hpair

theorem fuzzyFrameBalance_of_layerGenerationPair {𝒞 : MemberClass}
    (hpair : LayerGenerationPair) (hF3 : FuzzyNoF3 p f 𝒞) : FuzzyFrameBalance p f 𝒞 :=
  fuzzyFrameBalance_of_pairModelInputs (fuzzyPairModelInputs_of_layerGenerationPair hpair hF3)

end CFSG.ClassicalInvolution.Balance.Bootstrap
