module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Sporadic.HeldB.AutData
public import CFSG.Sporadic.HeldB.InnerRestrict

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier

@[expose] def HeldSylowElementarySixtyFour : Prop :=
  ∀ T : Subgroup (Equiv.Perm (Fin 8330)), T ≤ heP → Nat.card T = 1024 →
    ∃ E : Subgroup (Equiv.Perm (Fin 8330)), E ≤ T ∧ T ≤ normalizer (E : Set _) ∧
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x * x = 1) ∧ Nat.card E = 64

@[expose] def HeldOuterInvolutionRank : Prop :=
  ∀ T₀ : Subgroup (Equiv.Perm (Fin 8330)), T₀ ≤ heAutGroup → Nat.card T₀ = 2048 →
    ∀ a ∈ T₀, a ∉ heP → orderOf a = 2 →
      ∀ a₁ ∈ T₀ ⊓ heP, a₁ * a₁ = 1 → a₁ * a = a * a₁ →
        ∃ F : Subgroup (Equiv.Perm (Fin 8330)),
          F ≤ T₀ ⊓ heP ⊓ centralizer {a} ⊓ centralizer {a₁} ∧
          (∀ x ∈ F, ∀ y ∈ F, x * y = y * x) ∧ (∀ x ∈ F, x * x = 1) ∧ Nat.card F = 8

@[expose] def HeldFourGroupGeneration : Prop :=
  ∀ T : Subgroup (Equiv.Perm (Fin 8330)), T ≤ heP → Nat.card T = 1024 →
    (⨆ (B : Subgroup (Equiv.Perm (Fin 8330))) (_ : B ≤ T) (_ : Nat.card B = 4)
      (_ : ∀ x ∈ B, x * x = 1), heP ⊓ normalizer (B : Set _)) = heP

@[expose] def HeldSylowCenterTwo : Prop :=
  ∀ T : Subgroup (Equiv.Perm (Fin 8330)), T ≤ heP → Nat.card T = 1024 →
    Nat.card (center T) = 2

@[expose] def HeldTwoBCentralizerStructure : Prop :=
  ⁅centralizerIn heP heT1P, centralizerIn heP heT1P⁆ = centralizerIn heP heT1P ∧
    ∀ N : Subgroup (Equiv.Perm (Fin 8330)), N ≤ centralizerIn heP heT1P →
      (N.subgroupOf (centralizerIn heP heT1P)).Normal → N ≠ centralizerIn heP heT1P →
      IsPGroup 2 N

end CFSG.ComponentClassification.GrSLit
