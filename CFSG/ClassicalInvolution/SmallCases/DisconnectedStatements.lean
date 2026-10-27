module

public import CFSG.ClassicalInvolution.Generic.Induction
public import CFSG.ClassicalInvolution.SmallCases.Partition
public import CFSG.ClassicalInvolution.SmallCases.DisconnectedControl

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

abbrev CITDisconnectedControlled : Prop :=
  CITSimplePerfectUnder fun {F} _ _ _ K =>
    SmallConfiguration F K ∧ SL2Witness K ∧ ¬ DeltaConnected K ∧ ControlC K

abbrev CITDisconnectedUncontrolled : Prop :=
  CITSimplePerfectUnder fun {F} _ _ _ K =>
    SmallConfiguration F K ∧ SL2Witness K ∧ ¬ DeltaConnected K ∧ ¬ ControlC K

theorem citDisconnected_of_split (hc : CITDisconnectedControlled)
    (hu : CITDisconnectedUncontrolled) : CITDisconnected := by
  intro F _ _ _ hnab z hz K hzK hK hw hns h
  by_cases hC : ControlC K
  · exact hc F hnab z hz K hzK hK hw hns ⟨h.1, h.2.1, h.2.2, hC⟩
  · exact hu F hnab z hz K hzK hK hw hns ⟨h.1, h.2.1, h.2.2, hC⟩

section Statements

variable {F : Type*} [Group F]

@[expose] def CentralizerTwoRankOne (K : Subgroup F) : Prop :=
  ∀ a ∈ Subgroup.centralizer (K : Set F), ∀ b ∈ Subgroup.centralizer (K : Set F),
    orderOf a = 2 → orderOf b = 2 → a * b = b * a → a = b

@[expose] def NormalizerQuotientTwoGenerated (K : Subgroup F) : Prop :=
  ∀ P : Subgroup F, IsPGroup 2 P → P ≤ Subgroup.normalizer (K : Set F) →
    ∃ s : Finset F, s.card ≤ 2 ∧
      Subgroup.closure (s : Set F) ⊔ (P ⊓ Subgroup.centralizer (K : Set F)) = P

@[expose] def ControlSmallSylow : Prop :=
  ∀ (p f : ℕ) [Fact p.Prime], p ≠ 2 → 5 ≤ p ^ f →
    ∀ (F : Type) [Group F] [Finite F] [IsSimpleGroup F], CITBelowU p f (Nat.card F) →
      ∀ z : F, orderOf z = 2 → ∀ K : Subgroup F, z ∈ K →
        IsSubnormal K (Subgroup.centralizer ({z} : Set F)) →
        Nonempty (K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) →
        ¬ DeltaConnected K → ControlC K → ¬ SmallConfiguration F K

end Statements

end CFSG.ClassicalInvolution
