module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog
open scoped commutatorElement

@[expose] def CIrreducible (C : Type) [Group C] (Q : Subgroup C) : Prop :=
  ∀ W : Subgroup C, centerOf Q ≤ W → W ≤ Q →
    (∀ g ∈ commutator C, ∀ w ∈ W, g * w * g⁻¹ ∈ W) → W = centerOf Q ∨ W = Q

structure CSideFacts : Prop where
  mem_Q_of_cent : ∀ (C : Type) [Group C] (Q : Subgroup C) [Q.Normal],
    IsExtraspecialPlusByA5WrTwoWith C Q → ∀ a : C, a ^ 2 = 1 →
      IsShapeTwoTwoSixS5 ↥(Subgroup.centralizer ({a} : Set C)) → a ∈ Q
  rank_two : ∀ (C : Type) [Group C] (Q : Subgroup C) [Q.Normal],
    IsExtraspecialPlusByA5WrTwoWith C Q → ∀ E : Subgroup C, E ≤ Q →
      CFSG.Open.IsElemAbelian 2 E → Nat.card E ≤ 2 ^ 5
  inv_classes : ∀ (C : Type) [Group C] (Q : Subgroup C) [Q.Normal],
    IsExtraspecialPlusByA5WrTwoWith C Q → CIrreducible C Q →
      ∃ S : Fin 2 → Set C, IsOrbitPartition (⊤ : Subgroup C)
          {q | q ∈ Q ∧ q ^ 2 = 1 ∧ q ∉ centerOf Q} S ∧
        Nat.card ↥(S 0) = 150 ∧ Nat.card ↥(S 1) = 120
  three_local : ∀ (C : Type) [Group C] (Q : Subgroup C) [Q.Normal],
    IsExtraspecialPlusByA5WrTwoWith C Q → CIrreducible C Q →
      (∀ σ : C, orderOf σ = 3 →
        (IsShapeZpTimesA5 3 ↥(Subgroup.centralizer ({(σ : C ⧸ Q)} : Set (C ⧸ Q))) ∧
            Q ⊓ Subgroup.centralizer ({σ} : Set C) = centerOf Q) ∨
        (IsShapeZpWrTwo 3 ↥(Subgroup.centralizer ({(σ : C ⧸ Q)} : Set (C ⧸ Q))) ∧
            IsPlusExtraspecial 2 (Q ⊓ Subgroup.centralizer ({σ} : Set C)))) ∧
      (∃ σ : C, orderOf σ = 3 ∧
        IsShapeZpTimesA5 3 ↥(Subgroup.centralizer ({(σ : C ⧸ Q)} : Set (C ⧸ Q)))) ∧
      (∃ σ : C, orderOf σ = 3 ∧
        IsShapeZpWrTwo 3 ↥(Subgroup.centralizer ({(σ : C ⧸ Q)} : Set (C ⧸ Q))))
  five_local_shapes : ∀ (C : Type) [Group C] (Q : Subgroup C) [Q.Normal],
    IsExtraspecialPlusByA5WrTwoWith C Q → CIrreducible C Q →
      (∀ ρ : C, orderOf ρ = 5 →
        (IsShapeZpTimesA5 5 ↥(Subgroup.centralizer ({(ρ : C ⧸ Q)} : Set (C ⧸ Q))) ∧
            Q ⊓ Subgroup.centralizer ({ρ} : Set C) = centerOf Q) ∨
        IsShapeZpTimesZp 5 ↥(Subgroup.centralizer ({(ρ : C ⧸ Q)} : Set (C ⧸ Q))) ∨
        IsShapeZpWrTwo 5 ↥(Subgroup.centralizer ({(ρ : C ⧸ Q)} : Set (C ⧸ Q)))) ∧
      (∃ ρ : C, orderOf ρ = 5 ∧
        IsShapeZpTimesA5 5 ↥(Subgroup.centralizer ({(ρ : C ⧸ Q)} : Set (C ⧸ Q)))) ∧
      (∃ ρ : C, orderOf ρ = 5 ∧
        IsShapeZpTimesZp 5 ↥(Subgroup.centralizer ({(ρ : C ⧸ Q)} : Set (C ⧸ Q)))) ∧
      (∃ ρ : C, orderOf ρ = 5 ∧
        IsShapeZpWrTwo 5 ↥(Subgroup.centralizer ({(ρ : C ⧸ Q)} : Set (C ⧸ Q))))
  five_local : ∀ (C : Type) [Group C] (Q : Subgroup C) [Q.Normal],
    AschbacherHyp C Q → ∀ ρ : C, orderOf ρ = 5 →
        (IsShapeZpTimesA5 5 ↥(Subgroup.centralizer ({(ρ : C ⧸ Q)} : Set (C ⧸ Q))) ∧
            Q ⊓ Subgroup.centralizer ({ρ} : Set C) = centerOf Q) ∨
        (IsShapeZpTimesZp 5 ↥(Subgroup.centralizer ({(ρ : C ⧸ Q)} : Set (C ⧸ Q))) ∧
            IsMinusExtraspecial 2 (Q ⊓ Subgroup.centralizer ({ρ} : Set C))) ∨
        (IsShapeZpWrTwo 5 ↥(Subgroup.centralizer ({(ρ : C ⧸ Q)} : Set (C ⧸ Q))) ∧
            Q ⊓ Subgroup.centralizer ({ρ} : Set C) = centerOf Q)
  centQ_inv_base : ∀ (C : Type) [Group C] (Q : Subgroup C) [Q.Normal],
    IsExtraspecialPlusByA5WrTwoWith C Q → CIrreducible C Q → ∀ t : C,
      (t : C ⧸ Q) ^ 2 = 1 → (t : C ⧸ Q) ≠ 1 → (t : C ⧸ Q) ∈ commutator (C ⧸ Q) →
        Nat.card {q : C // q ∈ Q ∧ ⁅q, t⁆ ∈ centerOf Q} = 2 ^ 5
  centQ_inv : ∀ (C : Type) [Group C] (Q : Subgroup C) [Q.Normal],
    AschbacherHyp C Q → ∀ t : C, (t : C ⧸ Q) ^ 2 = 1 → (t : C ⧸ Q) ≠ 1 →
      Nat.card {q : C // q ∈ Q ∧ ⁅q, t⁆ ∈ centerOf Q} = 2 ^ 5
  hyp3_of_free : ∀ (C : Type) [Group C] (Q : Subgroup C) [Q.Normal],
    IsExtraspecialPlusByA5WrTwoWith C Q → CIrreducible C Q →
      ∀ t : C, t ∉ commutator C → t ^ 2 = 1 →
        Nat.card {q : C // q ∈ Q ∧ ⁅q, t⁆ ∈ centerOf Q} ≤ 2 ^ 5 →
          ∃ T : Sylow 2 C, t ∈ T ∧ ∃ x ∈ Q,
            (∀ s ∈ (T : Subgroup C) ⊓ commutator C, ⁅x, s⁆ ∈ centerOf Q) ∧
              ⁅t, x⁆ ∉ centerOf Q

end CFSG.EvenSporadicStandard.HNRecog.Section3
