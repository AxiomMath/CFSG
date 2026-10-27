module

public import CFSG.ClassicalInvolution.Q3.Q3JIStep3
public import CFSG.ClassicalInvolution.Q3.Q3IntrSat
public import CFSG.ClassicalInvolution.Q3.Q3ExIntr

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.JI

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

section Weak

@[expose] def CIT3LargeWeakJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      Asc77.CITBelowAll 3 (Nat.card G) → 3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G →
      Blueprint.OddLieType G ∨ Blueprint.NativeSporadic.IsSporadic G .M11

@[expose] def CIT3LargeIntrJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z →
      Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ K → CIT3Below (Nat.card G) →
      Asc77.CITBelowAll 3 (Nat.card G) → 3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G →
      Blueprint.OddLieType G ∨ Blueprint.NativeSporadic.IsSporadic G .M11

@[expose] def CIT3LargeUnderJ (P : ∀ {G : Type} [Group G], Subgroup G → G → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      Asc77.CITBelowAll 3 (Nat.card G) → 3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G →
      P K z → Blueprint.OddLieType G ∨ Blueprint.NativeSporadic.IsSporadic G .M11

@[expose] def SmallDisconnected3J : Prop :=
  CIT3LargeUnderJ fun K _ => ¬ DeltaConnected K

theorem cit3LargeWeakJ_of_intrinsicJ (h : CIT3LargeIntrJ) : CIT3LargeWeakJ :=
  fun G _ _ _ hnab _ z hK hBelow hAll h3 h4 =>
    h G hnab _ z (isClassicalMember3_sat hK) le_sup_right hBelow hAll h3 h4

end Weak

section Large

theorem coreStep3LargeJ_of_weakJ (h : CIT3LargeWeakJ) : CoreStep3LargeJ :=
  fun G _ _ _ hnab K z hK hBelow hAll h3 h4 =>
    smallUpgrade3_proved G hnab K z hK (h G hnab K z hK hBelow hAll h3 h4)

end Large

section Rec

theorem cit3LargeIntrJ_of_rec (hd : SmallDisconnected3J) (hrec : Q3W.SetupRecognition3I) :
    CIT3LargeIntrJ := by
  intro G _ _ _ hnab K z hz hint hBelow hAll h3 h4
  by_cases hΔ : DeltaConnected K
  · exact hrec G hnab K z hz hBelow h3 h4 hΔ
      (Q3NH.setup3_of_intrinsic_deltaConnected hnab hz hint hBelow hΔ) hint
  · exact hd G hnab K z hz hBelow hAll h3 h4 hΔ

end Rec

end CFSG.ClassicalInvolution.Q3.JI
