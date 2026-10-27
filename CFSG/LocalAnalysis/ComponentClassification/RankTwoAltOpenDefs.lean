module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveLocal
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenY

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint
  CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoClassical

@[expose] def AltFiveCaseI : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHyp G A →
    standardComponentOddCore G = ⊥ → Nonempty (rankTwoQuot A ≃* alternatingGroup (Fin 5)) →
    Odd (Nat.card (center ↥A)) → ∀ R : Subgroup G, IsSylowOf 2 R (centralizer (A : Set G)) →
    (∃ x : G, rightConjugate R x ≤ A) → Nonempty (rankTwoX A ≃* alternatingGroup (Fin 9))

@[expose] def AltFiveM12NotTop : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHyp G A →
    standardComponentOddCore G = ⊥ → Nonempty (rankTwoQuot A ≃* alternatingGroup (Fin 5)) →
    Odd (Nat.card (center ↥A)) → ∀ R : Subgroup G, IsSylowOf 2 R (centralizer (A : Set G)) →
    (∀ x : G, ¬ rightConjugate R x ≤ A) → NativeSporadic.IsSporadic (rankTwoX A) .M12 →
    (∃ t : G, t ^ 2 = 1 ∧ t ∈ normalizer (A : Set G) ∧ t ∈ normalizer (R : Set G) ∧
      ¬ ∃ a ∈ A, ∀ y ∈ A, t * y * t⁻¹ = a * y * a⁻¹) →
    rankTwoX A ≠ ⊤

@[expose] def AltEvenCenterSmall : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHyp G A →
    standardComponentOddCore G = ⊥ → ∀ n : ℕ, 5 ≤ n → n ≤ 7 →
    Nonempty (rankTwoQuot A ≃* alternatingGroup (Fin n)) → Odd (Nat.card (center ↥A))

@[expose] def AltThreeCover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHyp G A →
    standardComponentOddCore G = ⊥ → ∀ n : ℕ, 6 ≤ n → n ≤ 7 →
    Nonempty (rankTwoQuot A ≃* alternatingGroup (Fin n)) → Odd (Nat.card (center ↥A)) →
      center ↥A = ⊥

@[expose] def AltGenerationSmall : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R T : Subgroup G) (g : G) (n : ℕ)
    (Φ : alternatingGroup (Fin (n + 4)) →* G), (n = 6 ∨ n = 7) →
    AltGenSetting A R T g n Φ → rankTwoX A = A ⊔ rightConjugate A g

section Steps

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem hyp31_of (hH : RankTwoHyp G A) (hO : standardComponentOddCore G = ⊥) {n : ℕ}
    (hn : 5 ≤ n) (e : rankTwoQuot A ≃* alternatingGroup (Fin n)) : Hyp31 A :=
  ⟨hH.standard, hypII_of_alternating_ge_five hn hH.standard.1.1 e, hO,
    by have := hH.rank; omega, hH.not_normal⟩

theorem exists_sec3_of (hcfg : Section3Config) (hA : Hyp31 A) :
    ∃ (R T : Subgroup G) (g : G), Sec3 A R T g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := exists_isSylowOf 2 (centralizer (A : Set G))
  obtain ⟨g, hg, T, hT, -, hTR⟩ := RankTwoAltFive.exists_sec3 hcfg hA hR
  exact ⟨R, T, g, ⟨hA, hR, hg, hT, hTR⟩⟩

omit [Finite G] in
noncomputable def mulEquivOfCenter (hZ : center ↥A = ⊥) {n : ℕ}
    (e : rankTwoQuot A ≃* alternatingGroup (Fin n)) : ↥A ≃* alternatingGroup (Fin n) :=
  (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e

end Steps

end CFSG.ComponentClassification.RankTwoAlt
