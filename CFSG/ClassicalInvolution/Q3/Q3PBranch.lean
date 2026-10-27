module

public import CFSG.ClassicalInvolution.Q3.Q3PWeak

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

section Vocabulary

variable {G : Type} [Group G]

abbrev conjClass3 (K : Subgroup G) : Set (Subgroup G) :=
  Set.range fun g : G => conjSub g K

@[expose] def IndepTriple3 (Ω : Set (Subgroup G)) : Prop :=
  ∃ (K : Fin 3 → Subgroup G) (z : Fin 3 → G),
    (∀ i, K i ∈ Ω ∧ IsClassicalMember3 (K i) (z i)) ∧ (∀ i j, i ≠ j → Commutes (K i) (K j)) ∧
    IsElemAbelian 2 (Subgroup.closure (Set.range z)) ∧
    Nat.card (Subgroup.closure (Set.range z)) = 8

@[expose] def BootData3 (Ω : Set (Subgroup G)) : Prop :=
  ∃ (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G), L₀ ∈ Ω ∧ IsClassicalMember3 L₀ z₀ ∧
    IsElemAbelian 2 A ∧ Nat.card A = 8 ∧ z₀ ∈ A ∧ L₀ ≤ Subgroup.centralizer (A : Set G)

theorem IndepTriple3.bootData3 {Ω : Set (Subgroup G)} (h : IndepTriple3 Ω) : BootData3 Ω := by
  obtain ⟨K, z, hmem, hcomm, hA, hcard⟩ := h
  refine ⟨K 0, z 0, Subgroup.closure (Set.range z), (hmem 0).1, (hmem 0).2, hA, hcard,
    Subgroup.subset_closure ⟨0, rfl⟩, ?_⟩
  have h0 : K 0 ≤ Subgroup.centralizer ({z 0} : Set G) := isSubnormal_le (hmem 0).2.subnormal
  have hz : ∀ i, z i ∈ Subgroup.centralizer (K 0 : Set G) := by
    intro i
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    by_cases hi : i = 0
    · subst hi
      exact (Subgroup.mem_centralizer_iff.mp (h0 hk) (z 0) (Set.mem_singleton _)).symm
    · exact hcomm 0 i (Ne.symm hi) k hk (z i) (hmem i).2.mem
  have hA' : Subgroup.closure (Set.range z) ≤ Subgroup.centralizer (K 0 : Set G) :=
    (Subgroup.closure_le _).mpr (by rintro _ ⟨i, rfl⟩; exact hz i)
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact (Subgroup.mem_centralizer_iff.mp (hA' ha) k hk).symm

@[expose] def Setup3 (K : Subgroup G) (z : G) : Prop :=
  ExactMembers3 (conjClass3 K) ∧ LocalOddCentral (conjClass3 K) {z}

end Vocabulary

section Branches


@[expose] def CIT3LargeUnder (P : ∀ {G : Type} [Group G], Subgroup G → G → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → P K z →
      Blueprint.OddLieType G ∨ Blueprint.NativeSporadic.IsSporadic G .M11

@[expose] def GenericBranch3 : Prop :=
  CIT3LargeUnder fun K _ => DeltaConnected K ∧ BootData3 (conjClass3 K)

@[expose] def SmallDisconnected3 : Prop :=
  CIT3LargeUnder fun K _ => ¬ DeltaConnected K

@[expose] def SmallA2Connected3 : Prop :=
  CIT3LargeUnder fun K z => DeltaConnected K ∧ ¬ BootData3 (conjClass3 K) ∧ A2Configuration z K

@[expose] def SmallTypeC3 : Prop :=
  CIT3LargeUnder fun K z => DeltaConnected K ∧ ¬ BootData3 (conjClass3 K) ∧ ¬ A2Configuration z K

@[expose] def SmallA2Empty3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      A2Configuration z K → BootData3 (conjClass3 K)

theorem smallA2Connected3_of_empty (h : SmallA2Empty3) : SmallA2Connected3 := by
  rintro G _ _ _ hnab K z hz hBelow h3 h4 ⟨hΔ, hB, hA⟩
  exact absurd (h G hnab K z hz hBelow h3 h4 hΔ hA) hB

theorem cit3LargeWeak_of_branches (hg : GenericBranch3) (hd : SmallDisconnected3)
    (ha : SmallA2Connected3) (hc : SmallTypeC3) : CIT3LargeWeak := by
  intro G _ _ _ hnab K z hz hBelow h3 h4
  by_cases hΔ : DeltaConnected K
  · by_cases hB : BootData3 (conjClass3 K)
    · exact hg G hnab K z hz hBelow h3 h4 ⟨hΔ, hB⟩
    · by_cases hA : A2Configuration z K
      · exact ha G hnab K z hz hBelow h3 h4 ⟨hΔ, hB, hA⟩
      · exact hc G hnab K z hz hBelow h3 h4 ⟨hΔ, hB, hA⟩
  · exact hd G hnab K z hz hBelow h3 h4 hΔ

theorem branches_of_cit3LargeWeak (h : CIT3LargeWeak) :
    GenericBranch3 ∧ SmallDisconnected3 ∧ SmallA2Connected3 ∧ SmallTypeC3 :=
  ⟨fun G _ _ _ hnab K z hz hBelow h3 h4 _ => h G hnab K z hz hBelow h3 h4,
    fun G _ _ _ hnab K z hz hBelow h3 h4 _ => h G hnab K z hz hBelow h3 h4,
    fun G _ _ _ hnab K z hz hBelow h3 h4 _ => h G hnab K z hz hBelow h3 h4,
    fun G _ _ _ hnab K z hz hBelow h3 h4 _ => h G hnab K z hz hBelow h3 h4⟩

@[expose] def BootTriple3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      IndepTriple3 (conjClass3 K) → Setup3 K z

@[expose] def BootNoTriple3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      BootData3 (conjClass3 K) → ¬ IndepTriple3 (conjClass3 K) → Setup3 K z

@[expose] def SmallA2Setup3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      ¬ BootData3 (conjClass3 K) → A2Configuration z K → Setup3 K z

@[expose] def SmallTypeCSetup3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      ¬ BootData3 (conjClass3 K) → ¬ A2Configuration z K → Setup3 K z

@[expose] def SetupRecognition3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K → Setup3 K z →
      Blueprint.OddLieType G ∨ Blueprint.NativeSporadic.IsSporadic G .M11

theorem genericBranch3_of_pieces (hb3 : BootTriple3) (hb : BootNoTriple3)
    (hrec : SetupRecognition3) : GenericBranch3 := by
  rintro G _ _ _ hnab K z hz hBelow h3 h4 ⟨hΔ, hB⟩
  by_cases hT : IndepTriple3 (conjClass3 K)
  · exact hrec G hnab K z hz hBelow h3 h4 hΔ (hb3 G hnab K z hz hBelow h3 h4 hΔ hT)
  · exact hrec G hnab K z hz hBelow h3 h4 hΔ (hb G hnab K z hz hBelow h3 h4 hΔ hB hT)

theorem smallA2Connected3_of_setup (hs : SmallA2Setup3) (hrec : SetupRecognition3) :
    SmallA2Connected3 := by
  rintro G _ _ _ hnab K z hz hBelow h3 h4 ⟨hΔ, hB, hA⟩
  exact hrec G hnab K z hz hBelow h3 h4 hΔ (hs G hnab K z hz hBelow h3 h4 hΔ hB hA)

theorem smallTypeC3_of_setup (hs : SmallTypeCSetup3) (hrec : SetupRecognition3) :
    SmallTypeC3 := by
  rintro G _ _ _ hnab K z hz hBelow h3 h4 ⟨hΔ, hB, hA⟩
  exact hrec G hnab K z hz hBelow h3 h4 hΔ (hs G hnab K z hz hBelow h3 h4 hΔ hB hA)

theorem cit3LargeWeak_of_pieces (hd : SmallDisconnected3) (hb3 : BootTriple3)
    (hb : BootNoTriple3) (hsA : SmallA2Setup3) (hsC : SmallTypeCSetup3)
    (hrec : SetupRecognition3) : CIT3LargeWeak :=
  cit3LargeWeak_of_branches (genericBranch3_of_pieces hb3 hb hrec) hd
    (smallA2Connected3_of_setup hsA hrec) (smallTypeC3_of_setup hsC hrec)

end Branches

end CFSG.ClassicalInvolution.Q3
