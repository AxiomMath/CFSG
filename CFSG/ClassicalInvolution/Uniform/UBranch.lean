module

public import CFSG.ClassicalInvolution.Uniform.UIH8
public import CFSG.ClassicalInvolution.Uniform.USat

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
open scoped MatrixGroups

section Branch

variable (p f : ℕ)

structure DBranchU {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) : Prop where
  nonabelian : ∃ x y : G, x * y ≠ y * x
  odd : p ≠ 2
  three : 3 ≤ p ^ f
  below : CITBelowT (.sl2 p f) (Nat.card G)
  member : IsClassicalMemberU (.sl2 p f) K z
  rank : 3 ≤ CFSG.Open.twoRank G
  notFourGenerated : ¬ TwoSubgroupsFourGenerated G
  dDisconnected : ¬ DConnected (CoreAssembly.conjClass (satU (.sl2 p f) K z))

variable {p f}

namespace DBranchU

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem member_satU (h : DBranchU p f K z) :
    IsClassicalMemberU (.sl2 p f) (satU (.sl2 p f) K z) z :=
  h.member.satU_member

theorem intrinsic_satU (_h : DBranchU p f K z) :
    IsIntrinsicU (.sl2 p f) (satU (.sl2 p f) K z) z :=
  isIntrinsicU_satU _ K z

end DBranchU

@[expose] def HypOmegaModDU (p f : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchU p f K z → HypOmegaModU (.sl2 p f) (CoreAssembly.conjClass (satU (.sl2 p f) K z))

@[expose] def AEmptyDU (p f : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchU p f K z → ∀ J ∈ CoreAssembly.conjClass (satU (.sl2 p f) K z),
      AEmpty (CoreAssembly.conjClass (satU (.sl2 p f) K z)) J

@[expose] def IHAllDU (p f : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchU p f K z → CITBelowAllT p (Nat.card G)

@[expose] def IHInterface8U (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ n : ℕ, CITBelowAllT p n → IH8AllT p n

@[expose] def AscStandOfBranchU (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchU p f K z →
      AscStandT p f (CoreAssembly.conjClass (satU (.sl2 p f) K z)) (satU (.sl2 p f) K z)

end Branch

section Facades

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

omit [Fact p.Prime] [Finite G] in
theorem not_isSolvableType_sl2_of_five_le (hq : 5 ≤ p ^ f) :
    ¬ (MemberType.sl2 p f).IsSolvableType := fun h => by
  have h3 : p ^ f = 3 := h
  omega

theorem DBranchU.ofDBranchD (h : DBranchD p f K z) : DBranchU p f K z where
  nonabelian := h.nonabelian
  odd := h.odd
  three := by have := h.five; omega
  below := (citBelowT_iff_citBelowU h.odd h.five _).mpr h.below
  member := IsClassicalMemberU.ofGeneric h.odd
    (Nat.pos_of_ne_zero (by rintro rfl; have := h.five; simp at this)) h.member
  rank := h.rank
  notFourGenerated := h.notFourGenerated
  dDisconnected := by
    rw [satU_of_not_isSolvableType (not_isSolvableType_sl2_of_five_le h.five)]
    exact h.dDisconnected

theorem DBranchU.toDBranchD (h : DBranchU p f K z) (hq : 5 ≤ p ^ f) : DBranchD p f K z where
  nonabelian := h.nonabelian
  odd := h.odd
  five := hq
  below := (citBelowT_iff_citBelowU h.odd hq _).mp h.below
  member := h.member.toGeneric hq
  rank := h.rank
  notFourGenerated := h.notFourGenerated
  dDisconnected := by
    have := h.dDisconnected
    rwa [satU_of_not_isSolvableType (not_isSolvableType_sl2_of_five_le hq)] at this

theorem dBranchU_iff (hq : 5 ≤ p ^ f) : DBranchU p f K z ↔ DBranchD p f K z :=
  ⟨fun h => h.toDBranchD hq, DBranchU.ofDBranchD⟩

theorem hypOmegaModDU_iff (hq : 5 ≤ p ^ f) : HypOmegaModDU p f ↔ HypOmegaModD p f := by
  have hns := not_isSolvableType_sl2_of_five_le hq
  constructor
  · intro h G _ _ _ K z hb
    have := h G K z (DBranchU.ofDBranchD hb)
    rw [satU_of_not_isSolvableType hns] at this
    exact (hypOmegaModU_iff_hypOmegaMod hb.odd hq).mp this
  · intro h G _ _ _ K z hb
    rw [satU_of_not_isSolvableType hns]
    exact (hypOmegaModU_iff_hypOmegaMod hb.odd hq).mpr (h G K z (hb.toDBranchD hq))

theorem aEmptyDU_iff (hq : 5 ≤ p ^ f) : AEmptyDU p f ↔ AEmptyD p f := by
  have hns := not_isSolvableType_sl2_of_five_le hq
  constructor
  · intro h G _ _ _ K z hb J hJ
    have := h G K z (DBranchU.ofDBranchD hb)
    rw [satU_of_not_isSolvableType hns] at this
    exact this J hJ
  · intro h G _ _ _ K z hb J hJ
    rw [satU_of_not_isSolvableType hns] at hJ ⊢
    exact h G K z (hb.toDBranchD hq) J hJ

theorem ihAllDU_to_ihAllD (h : IHAllDU p f) : IHAllD p f :=
  fun G _ _ _ K z hb => (h G K z (DBranchU.ofDBranchD hb)).toAll hb.odd

theorem ihAllDU_of_ihAllD (hp3 : p ≠ 3) (hq : 5 ≤ p ^ f) (h : IHAllD p f) : IHAllDU p f :=
  fun G _ _ _ K z hb => (citBelowAllT_iff_citBelowAll hb.odd hp3 _).mpr
    (h G K z (hb.toDBranchD hq))

theorem ihInterface8U_iff (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    IHInterface8U p ↔ IHInterface8 p := by
  refine ⟨fun h n hn => ?_, fun h n hn => ?_⟩
  · exact (ih8AllT_iff_ih8All hp2 hp3 n).mp
      (h n ((citBelowAllT_iff_citBelowAll hp2 hp3 n).mpr hn))
  · exact (ih8AllT_iff_ih8All hp2 hp3 n).mpr
      (h n ((citBelowAllT_iff_citBelowAll hp2 hp3 n).mp hn))

theorem ihInterface8U_three_of (h : IHInterface8 3)
    (h3 : ∀ n : ℕ, CITBelowAll 3 n → Q3.CIT3Below n → IH8T 3 1 n) : IHInterface8U 3 :=
  fun n hn => by
    obtain ⟨h1, h2⟩ := (citBelowAllT_three_iff n).mp hn
    exact (ih8AllT_three_iff n).mpr ⟨h n h1, h3 n h1 h2⟩

theorem ihInterface8U_of_rest (hI : ∀ e : ℕ, 3 ≤ p ^ e → IHInterfaceU p e)
    (h : ∀ e : ℕ, 3 ≤ p ^ e → IH8RestU p e) : IHInterface8U p :=
  fun _ hn => ih8AllT_of_rest hI h hn

theorem ihInterface8U_three_of_rest (h : IHInterface8 3) (hI : IHInterfaceU 3 1)
    (hR : IH8RestU 3 1) : IHInterface8U 3 :=
  ihInterface8U_three_of h fun n _ h3 =>
    ih8T_of_rest hI hR ((citBelowT_three_iff (p := 3) (f := 1) (by norm_num) n).mpr h3)

theorem ascStandOfBranchU_to_ascStandOfBranch (hq : 5 ≤ p ^ f) (h : AscStandOfBranchU p f) :
    AscStandOfBranch p f := by
  have hns := not_isSolvableType_sl2_of_five_le hq
  intro G _ _ _ K z hb
  have := h G K z (DBranchU.ofDBranchD hb)
  rw [satU_of_not_isSolvableType hns] at this
  exact this.toAscStand hq

theorem ascStandOfBranchU_of_ascStandOfBranch (hp3 : p ≠ 3) (hq : 5 ≤ p ^ f)
    (h : AscStandOfBranch p f) : AscStandOfBranchU p f := by
  have hns := not_isSolvableType_sl2_of_five_le hq
  intro G _ _ _ K z hb
  rw [satU_of_not_isSolvableType hns]
  exact AscStandT.of_ascStand hp3 (h G K z (hb.toDBranchD hq))

end Facades

end CFSG.ClassicalInvolution.Uniform
