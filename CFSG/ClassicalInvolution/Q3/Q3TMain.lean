module

public import CFSG.ClassicalInvolution.Q3.Q3TAxis

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

@[expose] def TypeC3Rec : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      ¬ BootData3 (conjClass3 K) → ¬ A2Configuration z K → Setup3 K z →
      Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ K →
      Blueprint.OddLieType G ∨ Blueprint.NativeSporadic.IsSporadic G .M11

@[expose] def SmallTypeC3I : Prop :=
  CIT3LargeUnder fun K z => (DeltaConnected K ∧ ¬ BootData3 (conjClass3 K) ∧
    ¬ A2Configuration z K) ∧ Balance.oddCoreIn (Subgroup.centralizer ({z} : Set _)) ≤ K

theorem typeC3Rec_of_setupRecognition3 (h : SetupRecognition3) : TypeC3Rec := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ _ _ hS _
  exact h G hnab K z hz hBelow h3 h4 hΔ hS

theorem smallTypeCSetup3_of_alpha (hα : TypeC3Alpha) : SmallTypeCSetup3 := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hB hA2
  exact setup3_of_alpha hα hnab hz hBelow h3 h4 hΔ hB hA2

theorem smallTypeC3_of_alpha_rec (hα : TypeC3Alpha) (hrec : TypeC3Rec) : SmallTypeC3I := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 ⟨⟨hΔ, hB, hA2⟩, hint⟩
  exact hrec G hnab K z hz hBelow h3 h4 hΔ hB hA2
    (setup3_of_alpha hα hnab hz hBelow h3 h4 hΔ hB hA2) hint

theorem smallTypeC3_of_axes_rec (hax : TypeC3Axes) (hrec : TypeC3Rec) : SmallTypeC3I :=
  smallTypeC3_of_alpha_rec (typeC3Alpha_of_axes hax) hrec

theorem smallTypeC3_of_triangle_rest_rec (h1 : TypeC3Triangle) (h2 : TypeC3AxisRest)
    (hrec : TypeC3Rec) : SmallTypeC3I :=
  smallTypeC3_of_axes_rec (typeC3Axes_of_triangle_rest h1 h2) hrec

end CFSG.ClassicalInvolution.Q3
