module

public import CFSG.ClassicalInvolution.SmallCases.FrameRank
public import CFSG.ClassicalInvolution.PerfectCase

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

section Configuration

variable {G : Type*} [Group G]

@[expose] def A2Configuration (z : G) (J : Subgroup G) : Prop :=
  ∃ g h : G, J.map (MulAut.conj g⁻¹).toMonoidHom ≠ J.map (MulAut.conj h⁻¹).toMonoidHom ∧
    g⁻¹ * z * g ≠ h⁻¹ * z * h ∧
    (g⁻¹ * z * g) * (h⁻¹ * z * h) = (h⁻¹ * z * h) * (g⁻¹ * z * g) ∧
    ¬ Commutes (J.map (MulAut.conj g⁻¹).toMonoidHom) (J.map (MulAut.conj h⁻¹).toMonoidHom)

theorem case_partition' (z : G) (J : Subgroup G) :
    Group.IsSolvable J ∨ (¬ Group.IsSolvable J ∧ HasEFrameRank4 J) ∨
      (¬ Group.IsSolvable J ∧ ¬ HasEFrameRank4 J ∧ ¬ DeltaConnected J) ∨
      (¬ Group.IsSolvable J ∧ ¬ HasEFrameRank4 J ∧ DeltaConnected J ∧ A2Configuration z J) ∨
      (¬ Group.IsSolvable J ∧ ¬ HasEFrameRank4 J ∧ DeltaConnected J ∧ ¬ A2Configuration z J) := by
  by_cases hs : Group.IsSolvable J
  · exact Or.inl hs
  by_cases hf : HasEFrameRank4 J
  · exact Or.inr (Or.inl ⟨hs, hf⟩)
  by_cases hc : DeltaConnected J
  · by_cases ha : A2Configuration z J
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hs, hf, hc, ha⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hs, hf, hc, ha⟩)))
  · exact Or.inr (Or.inr (Or.inl ⟨hs, hf, hc⟩))

end Configuration

section PartOne

abbrev PartOneFrameRank4 : Prop :=
  PartOneUnder fun _ J => ¬ Group.IsSolvable J ∧ HasEFrameRank4 J

abbrev PartOneSmallDisconnected : Prop :=
  PartOneUnder fun _ J => ¬ Group.IsSolvable J ∧ ¬ HasEFrameRank4 J ∧ ¬ DeltaConnected J

abbrev PartOneSmallA2 : Prop :=
  PartOneUnder fun z J =>
    ¬ Group.IsSolvable J ∧ ¬ HasEFrameRank4 J ∧ DeltaConnected J ∧ A2Configuration z J

abbrev PartOneSmallTypeC : Prop :=
  PartOneUnder fun z J =>
    ¬ Group.IsSolvable J ∧ ¬ HasEFrameRank4 J ∧ DeltaConnected J ∧ ¬ A2Configuration z J

theorem partOne_of_cases' (hs : PartOneSolvable) (hf : PartOneFrameRank4)
    (hd : PartOneSmallDisconnected) (ha : PartOneSmallA2) (hc : PartOneSmallTypeC) : PartOne := by
  intro G _ _ _ hnab z hz J hzJ hJ S hS hw _
  rcases case_partition' z J with h | h | h | h | h
  · exact hs G hnab z hz J hzJ hJ S hS hw h
  · exact hf G hnab z hz J hzJ hJ S hS hw h
  · exact hd G hnab z hz J hzJ hJ S hS hw h
  · exact ha G hnab z hz J hzJ hJ S hS hw h
  · exact hc G hnab z hz J hzJ hJ S hS hw h

end PartOne

section Simple

@[expose] def SL2Witness {G : Type*} [Group G] (J : Subgroup G) : Prop :=
  ∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
    Nonempty (J ⧸ classicalInvolutionOddCore J ≃* SL(2, GaloisField p n))

@[expose] def A7Witness {G : Type*} [Group G] (J : Subgroup G) : Prop :=
  CFSG.Open.IsQuasisimple (J ⧸ classicalInvolutionOddCore J) ∧
    Nat.card (Subgroup.center (J ⧸ classicalInvolutionOddCore J)) = 2 ∧
    Nonempty ((J ⧸ classicalInvolutionOddCore J) ⧸
      Subgroup.center (J ⧸ classicalInvolutionOddCore J) ≃* alternatingGroup (Fin 7))

theorem classicalInvolutionWitness_iff {G : Type*} [Group G] (J : Subgroup G) :
    classicalInvolutionWitness J ↔ SL2Witness J ∨ A7Witness J :=
  Iff.rfl

@[expose] def TwoSubgroupsFourGenerated (F : Type*) [Group F] : Prop :=
  ∀ P : Subgroup F, IsPGroup 2 P → ∃ s : Finset F, s.card ≤ 4 ∧ Subgroup.closure (s : Set F) = P

@[expose] def CITSimplePerfectUnder
    (P : ∀ {F : Type} [Group F] [Finite F], F → Subgroup F → Prop) : Prop :=
  ∀ (F : Type) [Group F] [Finite F] [IsSimpleGroup F], (∃ a b : F, a * b ≠ b * a) →
    ∀ z : F, orderOf z = 2 → ∀ K : Subgroup F, z ∈ K →
    IsSubnormal K (Subgroup.centralizer ({z} : Set F)) → classicalInvolutionWitness K →
    ¬ Group.IsSolvable K → P z K →
    Blueprint.OddLieType F ∨ Blueprint.NativeSporadic.IsSporadic F .M11

@[expose] def SmallConfiguration (F : Type) [Group F] [Finite F] (K : Subgroup F) : Prop :=
  3 ≤ twoRank F ∧ ¬ TwoSubgroupsFourGenerated F ∧ ¬ HasEFrameRank4 K

abbrev CITFrameRankFour : Prop :=
  CITSimplePerfectUnder fun _ K => HasEFrameRank4 K

abbrev CITRankTwo : Prop :=
  CITSimplePerfectUnder fun {F} _ _ _ _ => twoRank F ≤ 2

abbrev CITSectionalFour : Prop :=
  CITSimplePerfectUnder fun {F} _ _ _ _ => 3 ≤ twoRank F ∧ TwoSubgroupsFourGenerated F

abbrev CIT2A7 : Prop :=
  CITSimplePerfectUnder fun {F} _ _ _ K => SmallConfiguration F K ∧ A7Witness K

abbrev CITDisconnected : Prop :=
  CITSimplePerfectUnder fun {F} _ _ _ K =>
    SmallConfiguration F K ∧ SL2Witness K ∧ ¬ DeltaConnected K

abbrev CITConnectedA2 : Prop :=
  CITSimplePerfectUnder fun {F} _ _ z K =>
    SmallConfiguration F K ∧ SL2Witness K ∧ DeltaConnected K ∧ A2Configuration z K

abbrev CITTypeC : Prop :=
  CITSimplePerfectUnder fun {F} _ _ z K =>
    SmallConfiguration F K ∧ SL2Witness K ∧ DeltaConnected K ∧ ¬ A2Configuration z K

theorem citSimplePerfect_of_cases (hF : CITFrameRankFour) (h0 : CITRankTwo)
    (h1 : CITSectionalFour) (h2 : CIT2A7) (h3 : CITDisconnected) (h4 : CITConnectedA2)
    (h5 : CITTypeC) : CITSimplePerfect := by
  intro F _ _ _ hnab z hz K hzK hK hw hns
  by_cases hf : HasEFrameRank4 K
  · exact hF F hnab z hz K hzK hK hw hns hf
  by_cases hr : twoRank F ≤ 2
  · exact h0 F hnab z hz K hzK hK hw hns hr
  by_cases hs : TwoSubgroupsFourGenerated F
  · exact h1 F hnab z hz K hzK hK hw hns ⟨by omega, hs⟩
  have hsmall : SmallConfiguration F K := ⟨by omega, hs, hf⟩
  rcases (classicalInvolutionWitness_iff K).mp hw with hsl | ha7
  · by_cases hc : DeltaConnected K
    · by_cases ha : A2Configuration z K
      · exact h4 F hnab z hz K hzK hK hw hns ⟨hsmall, hsl, hc, ha⟩
      · exact h5 F hnab z hz K hzK hK hw hns ⟨hsmall, hsl, hc, ha⟩
    · exact h3 F hnab z hz K hzK hK hw hns ⟨hsmall, hsl, hc⟩
  · exact h2 F hnab z hz K hzK hK hw hns ⟨hsmall, ha7⟩

theorem citSimplePerfectUnder_of_citSimplePerfect (h : CITSimplePerfect)
    (P : ∀ {F : Type} [Group F] [Finite F], F → Subgroup F → Prop) : CITSimplePerfectUnder P :=
  fun F _ _ _ hnab z hz K hzK hK hw hns _ => h F hnab z hz K hzK hK hw hns

theorem citSimplePerfect_iff_cases :
    CITSimplePerfect ↔ CITFrameRankFour ∧ CITRankTwo ∧ CITSectionalFour ∧ CIT2A7 ∧
      CITDisconnected ∧ CITConnectedA2 ∧ CITTypeC :=
  ⟨fun h => by
    have h' := citSimplePerfectUnder_of_citSimplePerfect h
    exact ⟨h' _, h' _, h' _, h' _, h' _, h' _, h' _⟩,
    fun ⟨hF, h0, h1, h2, h3, h4, h5⟩ => citSimplePerfect_of_cases hF h0 h1 h2 h3 h4 h5⟩

end Simple

end CFSG.ClassicalInvolution
