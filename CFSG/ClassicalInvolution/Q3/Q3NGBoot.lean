module

public import CFSG.ClassicalInvolution.Q3.Q3PStage
public import CFSG.ClassicalInvolution.Q3.Stage2
import CFSG.ClassicalInvolution.Q3.Q3TSetup

public section

namespace CFSG.ClassicalInvolution.Q3.Q3NG

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

section Defs

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

structure BootTripleSetting3 (K : Subgroup G) (z : G) : Prop where
  nonabelian : ∃ a b : G, a * b ≠ b * a
  member : IsClassicalMember3 K z
  below : CIT3Below (Nat.card G)
  rank : 3 ≤ twoRank G
  notFourGenerated : ¬ TwoSubgroupsFourGenerated G
  delta : DeltaConnected K
  triple : IndepTriple3 (conjClass3 K)

structure ClassTriple3 (K K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ : G) : Prop where
  exact : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃
  ind : z₁ * z₂ ≠ z₃
  mem₁ : K₁ ∈ conjClass3 K
  mem₂ : K₂ ∈ conjClass3 K
  mem₃ : K₃ ∈ conjClass3 K
  cls₁ : IsClassicalMember3 K₁ z₁
  cls₂ : IsClassicalMember3 K₂ z₂
  cls₃ : IsClassicalMember3 K₃ z₃

end Defs

@[expose] def SingleClassComponents3At : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    BootTripleSetting3 K z → ∀ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ : G),
      ∀ T : ClassTriple3 K K₁ K₂ K₃ z₁ z₂ z₃, ∀ a ∈ T.exact.group, a ≠ 1 →
        ∀ (ι : Type) (D : LieSystemData3 ι (LocalQuot (conjClass3 K) a)
          (localFamily (conjClass3 K) a)), SingleClassComponents3 D

@[expose] def CentralizerGenerationModOTwoAt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    BootTripleSetting3 K z → ∀ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ : G),
      ∀ T : ClassTriple3 K K₁ K₂ K₃ z₁ z₂ z₃, ∀ a ∈ T.exact.group,
        IsFrameInvolution3 (frameFamily3 (conjClass3 K) T.exact.group) a →
          CentralizerGenerationModOTwo (conjClass3 K) T.exact.group a

@[expose] def LieCovers3At : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    BootTripleSetting3 K z → ∀ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ : G),
      ∀ T : ClassTriple3 K K₁ K₂ K₃ z₁ z₂ z₃, ∀ a ∈ T.exact.group,
        IsFrameInvolution3 (frameFamily3 (conjClass3 K) T.exact.group) a →
          LieCovers3 (conjClass3 K) (frameFamily3 (conjClass3 K) T.exact.group) a

@[expose] def P1Cover3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    BootTripleSetting3 K z → ∀ L ∈ conjClass3 K, L ≤ Subgroup.centralizer ({z} : Set G) →
      ∃ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ : G) (T : ClassTriple3 K K₁ K₂ K₃ z₁ z₂ z₃),
        z ∈ T.exact.group ∧ ∃ F ∈ signalizerFunctorEk 2 2 T.exact.group, z ∈ F ∧
          L ≤ Subgroup.centralizer (F : Set G)

section Stage2

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem stage2_of_classTriple3 (hKG1 : LieLocallyTwoBalanced3) (hM11 : M11LocallyTwoBalanced)
    (hMF1 : SingleClassComponents3At) (hgen : CentralizerGenerationModOTwoAt)
    (hcov : LieCovers3At) {K : Subgroup G} {z : G} (hS : BootTripleSetting3 K z)
    {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G} (T : ClassTriple3 K K₁ K₂ K₃ z₁ z₂ z₃) :
    (∀ F ∈ signalizerFunctorEk 2 2 T.exact.group, deltaCore F = ⊥) ∧
      StronglyBalanced T.exact.group ∧ classicalInvolutionOddCore ↥K₁ = ⊥ ∧
      classicalInvolutionOddCore ↥K₂ = ⊥ ∧ classicalInvolutionOddCore ↥K₃ = ⊥ := by
  have hΩ : InClass3 (conjClass3 K) := inClass3_conjugates hS.member
  have hIH : LocalLieSystems3 (conjClass3 K) := localLieSystems3_of_cit3Below hΩ hS.below
  have hO : LocalOddCentralizer3 (conjClass3 K) :=
    localOddCentralizer3_of_lieSystem lieSystemOddCentralizer3_proved hIH
  have hnc : ∀ b : G, b ≠ 1 → b ∉ Subgroup.center G := fun b hb1 hbc =>
    not_subset_center_of_ne_one hS.nonabelian hb1 (Set.singleton_subset_iff.mpr hbc)
  exact stage2_of_exactTriple3_of_model ModelFacts.modelClauseZero m11Facts hKG1 hM11
    (componentClassificationOddCore_eq_bot_of_simple hS.nonabelian) hΩ hIH hO T.exact T.ind
    T.mem₁ T.mem₂ T.mem₃ T.cls₁ T.cls₂ T.cls₃ (fun b _ hb1 => hnc b hb1)
    (hMF1 G K z hS K₁ K₂ K₃ z₁ z₂ z₃ T) (omegaConnected_range_conjSub hS.delta)
    (hgen G K z hS K₁ K₂ K₃ z₁ z₂ z₃ T) (hcov G K z hS K₁ K₂ K₃ z₁ z₂ z₃ T)

end Stage2

theorem bootTriple3_of (hKG1 : LieLocallyTwoBalanced3) (hM11 : M11LocallyTwoBalanced)
    (hMF1 : SingleClassComponents3At) (hgen : CentralizerGenerationModOTwoAt)
    (hcov : LieCovers3At) (hP1 : P1Cover3) : BootTriple3 := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hT
  have hS : BootTripleSetting3 K z := ⟨hnab, hz, hBelow, h3, h4, hΔ, hT⟩
  have hΩ : InClass3 (conjClass3 K) := inClass3_conjugates hz
  have hIH : LocalLieSystems3 (conjClass3 K) := localLieSystems3_of_cit3Below hΩ hBelow
  have hO : LocalOddCentralizer3 (conjClass3 K) :=
    localOddCentralizer3_of_lieSystem lieSystemOddCentralizer3_proved hIH
  have hnc : ∀ b : G, b ≠ 1 → b ∉ Subgroup.center G := fun b hb1 hbc =>
    not_subset_center_of_ne_one hnab hb1 (Set.singleton_subset_iff.mpr hbc)
  obtain ⟨K₁, K₂, K₃, z₁, z₂, z₃, hE, hind, ⟨h₁, hz₁⟩, ⟨h₂, hz₂⟩, ⟨h₃, hz₃⟩⟩ :=
    hT.exists_exactTriple
  have T₀ : ClassTriple3 K K₁ K₂ K₃ z₁ z₂ z₃ := ⟨hE, hind, h₁, h₂, h₃, hz₁, hz₂, hz₃⟩
  obtain ⟨-, -, hex₁, -, -⟩ := stage2_of_classTriple3 hKG1 hM11 hMF1 hgen hcov hS T₀
  obtain ⟨b, hb⟩ := h₁
  have hexact : ExactMembers3 (conjClass3 K) := by
    refine exactMembers3_of_conjugates hex₁ fun L hL => ?_
    obtain ⟨a, rfl⟩ := hL
    refine ⟨a * b⁻¹, ?_⟩
    show conjSub a K = conjSub (a * b⁻¹) K₁
    rw [← hb, ← conjSub_mul]
    simp
  refine ⟨hexact, localOddCentral3_of_members_centralize hΩ.conjInvariant fun L hLΩ hLz => ?_⟩
  obtain ⟨M₁, M₂, M₃, w₁, w₂, w₃, T, hzT, F, hF, hzF, hLF⟩ := hP1 G K z hS L hLΩ hLz
  obtain ⟨hΔT, hSB, -⟩ := stage2_of_classTriple3 hKG1 hM11 hMF1 hgen hcov hS T
  exact le_centralizer_involutionOddCore_of_covered hΩ.conjInvariant hO T.exact.isElemAbelian
    (fun c hc _ => group_le_centralizingLayer_of_exactTriple T.exact T.mem₁ T.mem₂ T.mem₃ hc)
    (fun c _ hc1 => hnc c hc1) hSB hΔT hzT hz.ne_one hLΩ hLz hF hzF hLF

end CFSG.ClassicalInvolution.Q3.Q3NG
