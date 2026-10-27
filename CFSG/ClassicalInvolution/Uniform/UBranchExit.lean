module

public import CFSG.ClassicalInvolution.Uniform.UBranchProof
public import CFSG.ClassicalInvolution.Q3.Q3PBranch

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
open scoped MatrixGroups

section Statements

variable (p f : ℕ) [Fact p.Prime]

@[expose] def Thm6AU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    AscStandT p f Ω K → DEdgeless Ω → ConcOrTF4 G

@[expose] def Thm7AU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    AscStandT p f Ω K → (∃ K' ∈ twinSet Ω K, K' ≠ K) → ¬ DConnected Ω → ConcOrTF4 G

@[expose] def Thm8AU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    AscStandT p f Ω K → ¬ DEdgeless Ω → (∀ K' ∈ twinSet Ω K, K' = K) → ¬ DConnected Ω → False

@[expose] def Thm6DU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchU p f K z → DEdgeless (CoreAssembly.conjClass (satU (.sl2 p f) K z)) → ConclusionD G

@[expose] def Thm7DU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchU p f K z → ¬ DEdgeless (CoreAssembly.conjClass (satU (.sl2 p f) K z)) →
      (∃ K' ∈ twinSet (CoreAssembly.conjClass (satU (.sl2 p f) K z)) (satU (.sl2 p f) K z),
        K' ≠ satU (.sl2 p f) K z) → ConclusionD G

@[expose] def Thm8DU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchU p f K z → ¬ DEdgeless (CoreAssembly.conjClass (satU (.sl2 p f) K z)) →
      (∀ K' ∈ twinSet (CoreAssembly.conjClass (satU (.sl2 p f) K z)) (satU (.sl2 p f) K z),
        K' = satU (.sl2 p f) K z) → False

@[expose] def SmallDisconnectedDU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchU p f K z → ConclusionD G

@[expose] def DBridgeU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 3 ≤ p ^ f → CITBelowT (.sl2 p f) (Nat.card G) → ∀ (K : Subgroup G) (z : G),
      IsClassicalMemberU (.sl2 p f) K z → 3 ≤ CFSG.Open.twoRank G →
      ¬ TwoSubgroupsFourGenerated G →
      DConnected (CoreAssembly.conjClass (satU (.sl2 p f) K z)) →
      CFSG.ClassicalInvolution.DeltaConnected K

@[expose] def SmallDisconnectedU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 3 ≤ p ^ f → CITBelowT (.sl2 p f) (Nat.card G) → ∀ (K : Subgroup G) (z : G),
      IsClassicalMemberU (.sl2 p f) K z → 3 ≤ CFSG.Open.twoRank G →
      ¬ TwoSubgroupsFourGenerated G → ¬ CFSG.ClassicalInvolution.DeltaConnected K →
      ConclusionD G

end Statements

section Proofs

variable {p f : ℕ} [Fact p.Prime]

theorem thm6DU_of_thm6AU (hs : AscStandOfBranchU p f) (h : Thm6AU p f) : Thm6DU p f :=
  fun G _ _ _ K z hb hE =>
    (h G _ (satU (.sl2 p f) K z) (hs G K z hb) hE).conclusionD hb.notFourGenerated

theorem thm7DU_of_thm7AU (hs : AscStandOfBranchU p f) (h : Thm7AU p f) : Thm7DU p f :=
  fun G _ _ _ K z hb _ hT =>
    (h G _ (satU (.sl2 p f) K z) (hs G K z hb) hT hb.dDisconnected).conclusionD
      hb.notFourGenerated

theorem thm8DU_of_thm8AU (hs : AscStandOfBranchU p f) (h : Thm8AU p f) : Thm8DU p f :=
  fun G _ _ _ K z hb hE hT =>
    h G _ (satU (.sl2 p f) K z) (hs G K z hb) hE hT hb.dDisconnected

omit [Fact p.Prime] in
theorem smallDisconnectedDU_of_aschbacher (h6 : Thm6DU p f) (h7 : Thm7DU p f) (h8 : Thm8DU p f) :
    SmallDisconnectedDU p f := by
  intro G _ _ _ K z hb
  by_cases hE : DEdgeless (CoreAssembly.conjClass (satU (.sl2 p f) K z))
  · exact h6 G K z hb hE
  · by_cases hT : ∃ K' ∈ twinSet (CoreAssembly.conjClass (satU (.sl2 p f) K z))
        (satU (.sl2 p f) K z), K' ≠ satU (.sl2 p f) K z
    · exact h7 G K z hb hE hT
    · exact (h8 G K z hb hE fun K' hK' => by_contra fun hne => hT ⟨K', hK', hne⟩).elim

theorem smallDisconnectedDU_of_inputs (hΩ : HypOmegaModDU p f) (hA : AEmptyDU p f)
    (hall : IHAllDU p f) (hih : IHInterface8U p) (h6 : Thm6AU p f) (h7 : Thm7AU p f)
    (h8 : Thm8AU p f) : SmallDisconnectedDU p f :=
  have hs := ascStandOfBranchU_of hΩ hA hall hih
  smallDisconnectedDU_of_aschbacher (thm6DU_of_thm6AU hs h6) (thm7DU_of_thm7AU hs h7)
    (thm8DU_of_thm8AU hs h8)

omit [Fact p.Prime] in
theorem smallDisconnectedU_of_dBridgeU (hb : DBridgeU p f) (hs : SmallDisconnectedDU p f) :
    SmallDisconnectedU p f := by
  intro G _ _ _ hnab hp2 hq hBelow K z hz h3 h4 hΔ
  by_cases hD : DConnected (CoreAssembly.conjClass (satU (.sl2 p f) K z))
  · exact absurd (hb G hnab hp2 hq hBelow K z hz h3 h4 hD) hΔ
  · exact hs G K z ⟨hnab, hp2, hq, hBelow, hz, h3, h4, hD⟩

omit [Fact p.Prime] in
theorem smallDisconnectedU_of_aschbacher (hb : DBridgeU p f) (h6 : Thm6DU p f) (h7 : Thm7DU p f)
    (h8 : Thm8DU p f) : SmallDisconnectedU p f :=
  smallDisconnectedU_of_dBridgeU hb (smallDisconnectedDU_of_aschbacher h6 h7 h8)

end Proofs

section Facades

variable {p f : ℕ} [Fact p.Prime]

theorem thm6AU_of_thm6A (hq : 5 ≤ p ^ f) (h : Thm6A p f) : Thm6AU p f :=
  fun G _ _ _ Ω K hS hE => h G Ω K (hS.toAscStand hq) hE

theorem thm6A_of_thm6AU (hp3 : p ≠ 3) (h : Thm6AU p f) : Thm6A p f :=
  fun G _ _ _ Ω K hS hE => h G Ω K (AscStandT.of_ascStand hp3 hS) hE

theorem thm7AU_of_thm7A (hq : 5 ≤ p ^ f) (h : Thm7A p f) : Thm7AU p f :=
  fun G _ _ _ Ω K hS hT hD => h G Ω K (hS.toAscStand hq) hT hD

theorem thm7A_of_thm7AU (hp3 : p ≠ 3) (h : Thm7AU p f) : Thm7A p f :=
  fun G _ _ _ Ω K hS hT hD => h G Ω K (AscStandT.of_ascStand hp3 hS) hT hD

theorem thm8AU_of_thm8A (hq : 5 ≤ p ^ f) (h : Thm8A p f) : Thm8AU p f :=
  fun G _ _ _ Ω K hS hE hT hD => h G Ω K (hS.toAscStand hq) hE hT hD

theorem thm8A_of_thm8AU (hp3 : p ≠ 3) (h : Thm8AU p f) : Thm8A p f :=
  fun G _ _ _ Ω K hS hE hT hD => h G Ω K (AscStandT.of_ascStand hp3 hS) hE hT hD

theorem dBridgeU_iff (hq : 5 ≤ p ^ f) : DBridgeU p f ↔ DBridge p f := by
  have hns := not_isSolvableType_sl2_of_five_le hq
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  constructor
  · intro h G _ _ _ hnab hp2 _ hBelow K z hz h3 h4 hD
    rw [← satU_of_not_isSolvableType hns (K := K) (z := z)] at hD
    exact h G hnab hp2 (by omega) ((citBelowT_iff_citBelowU hp2 hq _).mpr hBelow) K z
      (IsClassicalMemberU.ofGeneric hp2 hf hz) h3 h4 hD
  · intro h G _ _ _ hnab hp2 _ hBelow K z hz h3 h4 hD
    rw [satU_of_not_isSolvableType hns] at hD
    exact h G hnab hp2 hq ((citBelowT_iff_citBelowU hp2 hq _).mp hBelow) K z (hz.toGeneric hq) h3
      h4 hD

theorem smallDisconnectedU_iff (hq : 5 ≤ p ^ f) :
    SmallDisconnectedU p f ↔ CoreAssembly.SmallDisconnected p f := by
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  constructor
  · intro h G _ _ _ hnab hp2 _ hBelow K z hz h3 h4 hΔ
    exact h G hnab hp2 (by omega) ((citBelowT_iff_citBelowU hp2 hq _).mpr hBelow) K z
      (IsClassicalMemberU.ofGeneric hp2 hf hz) h3 h4 hΔ
  · intro h G _ _ _ hnab hp2 _ hBelow K z hz h3 h4 hΔ
    exact h G hnab hp2 hq ((citBelowT_iff_citBelowU hp2 hq _).mp hBelow) K z (hz.toGeneric hq) h3
      h4 hΔ

theorem thm6AU_iff (hp3 : p ≠ 3) (hq : 5 ≤ p ^ f) : Thm6AU p f ↔ Thm6A p f :=
  ⟨thm6A_of_thm6AU hp3, thm6AU_of_thm6A hq⟩

theorem thm7AU_iff (hp3 : p ≠ 3) (hq : 5 ≤ p ^ f) : Thm7AU p f ↔ Thm7A p f :=
  ⟨thm7A_of_thm7AU hp3, thm7AU_of_thm7A hq⟩

theorem thm8AU_iff (hp3 : p ≠ 3) (hq : 5 ≤ p ^ f) : Thm8AU p f ↔ Thm8A p f :=
  ⟨thm8A_of_thm8AU hp3, thm8AU_of_thm8A hq⟩

theorem smallDisconnectedU_three_iff : SmallDisconnectedU 3 1 ↔ Q3.SmallDisconnected3 := by
  constructor
  · intro h G _ _ _ hnab K z hz hB h3 h4 hΔ
    exact h G hnab (by norm_num) (by norm_num)
      ((citBelowT_three_iff (p := 3) (f := 1) (by norm_num) _).mpr hB) K z
      (IsClassicalMemberU.ofQ3 hz) h3 h4 hΔ
  · intro h G _ _ _ hnab _ _ hB K z hz h3 h4 hΔ
    exact h G hnab K z (hz.toQ3 (by norm_num))
      ((citBelowT_three_iff (p := 3) (f := 1) (by norm_num) _).mp hB) h3 h4 hΔ

end Facades

end CFSG.ClassicalInvolution.Uniform
