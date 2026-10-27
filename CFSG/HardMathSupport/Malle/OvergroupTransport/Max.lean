module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbedding.ReeF4Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Malle.OvergroupTransport

open CFSG.AGLEmbedding CFSG.Open Subgroup

@[expose] def ReeF4SocleLineData : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex),
    IsReeFFourFiveIndex d → Nonempty (K ≃* CatGroup d) → ∀ P : Sylow 5 K,
    ∃ Z : Subgroup K, (∀ y, y ∈ Z ↔ y ∈ (P : Subgroup K) ∧ y ^ 5 = 1) ∧
      (∀ a ∈ (P : Subgroup K), ∀ b ∈ (P : Subgroup K), a * b = b * a) ∧ Nat.card Z = 5 ^ 2 ∧
      (∀ x ∈ Z, x ≠ 1 → ∀ H : Subgroup K,
        normalizer ((P : Subgroup K) : Set K) ⊓ centralizer ({x} : Set K) ≤ H →
          H ≤ centralizer ({x} : Set K) →
            H = normalizer ((P : Subgroup K) : Set K) ⊓ centralizer ({x} : Set K) ∨
              H = centralizer ({x} : Set K)) ∧
      (∀ x ∈ Z, x ≠ 1 → ∀ y ∈ Z, y ≠ 1 →
        ∃ n ∈ normalizer ((P : Subgroup K) : Set K), ∀ g : K,
          g ∈ centralizer ({y} : Set K) → n⁻¹ * g * n ∈ centralizer ({x} : Set K))

end CFSG.HardMathSupport.Malle.OvergroupTransport
