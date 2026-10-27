module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2411Core
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2411L34Proof
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_6
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Mathieu.M23

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open CFSG.QuasithinUnique.Vol2Native
open scoped MatrixGroups

section Generic

variable {K : Type*} [Group K] [Finite K]

theorem pCore_two_le_center [Group.IsPerfect K] (hs : IsSimpleGroup (K ⧸ Subgroup.center K)) :
    CFSG.pCore 2 K ≤ Subgroup.center K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (CFSG.pCore 2 K).Normal := CFSG.pCore_normal
  have hmap : ((CFSG.pCore 2 K).map (QuotientGroup.mk' (Subgroup.center K))).Normal :=
    Subgroup.Normal.map hN _ (QuotientGroup.mk'_surjective _)
  rcases hs.eq_bot_or_eq_top_of_normal
      ((CFSG.pCore 2 K).map (QuotientGroup.mk' (Subgroup.center K))) with h | h
  · intro n hn
    have h1 : QuotientGroup.mk' (Subgroup.center K) n ∈
        (CFSG.pCore 2 K).map (QuotientGroup.mk' (Subgroup.center K)) := ⟨n, hn, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff n).1 h1
  · exfalso
    have h2 : IsPGroup 2 ((CFSG.pCore 2 K).map (QuotientGroup.mk' (Subgroup.center K))) :=
      (CFSG.pCore_isPGroup (p := 2) (G := K)).map _
    rw [h] at h2
    have h3 : IsPGroup 2 (K ⧸ Subgroup.center K) := h2.of_equiv Subgroup.topEquiv
    have h4 : Group.IsNilpotent (K ⧸ Subgroup.center K) := h3.isNilpotent
    have := hs.toNontrivial
    exact Group.IsPerfect.not_isNilpotent (K ⧸ Subgroup.center K) h4

end Generic

section Quasisimple

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pCoreOf_eq_bot_of_pCore_eq_bot {K : Subgroup G} (h : CFSG.pCore 2 ↥K = ⊥) :
    pCoreOf 2 K = ⊥ := by
  unfold pCoreOf
  rw [h, Subgroup.map_bot]

theorem center_eq_bot_of_simple {K : Type*} [Group K] [Group.IsPerfect K] (hs : IsSimpleGroup K) :
    Subgroup.center K = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · exact h
  · exfalso
    have := hs.toNontrivial
    have hc : IsMulCommutative K := by
      refine ⟨⟨fun a b => ?_⟩⟩
      have ha : a ∈ Subgroup.center K := by rw [h]; trivial
      exact (Subgroup.mem_center_iff.1 ha b).symm
    exact Group.IsPerfect.not_isMulCommutative (G := K) hc

theorem pCoreOf_eq_bot_of_simple {K : Subgroup G} (hq : CFSG.IsQuasisimple ↥K)
    (hs : IsSimpleGroup ↥K) : pCoreOf 2 K = ⊥ := by
  have : Group.IsPerfect ↥K := hq.1
  have h1 := pCore_two_le_center hq.2.1
  rw [center_eq_bot_of_simple hs] at h1
  exact pCoreOf_eq_bot_of_pCore_eq_bot (le_bot_iff.1 h1)

theorem pCoreOf_eq_bot_of_card_center {K : Subgroup G} (hq : CFSG.IsQuasisimple ↥K)
    (hc : Nat.card (Subgroup.center ↥K) = 3) : pCoreOf 2 K = ⊥ := by
  have : Group.IsPerfect ↥K := hq.1
  have h1 := pCore_two_le_center hq.2.1
  have h2 : Nat.card (CFSG.pCore 2 ↥K) ∣ 3 := hc ▸ Subgroup.card_dvd_of_le h1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := ↥K))
  rw [hk] at h2
  have h3 : Nat.card (CFSG.pCore 2 ↥K) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 h2 with h | h
    · rw [hk, h]
    · exfalso
      rcases k with _ | k
      · simp at h
      · rw [Nat.pow_succ] at h
        omega
  exact pCoreOf_eq_bot_of_pCore_eq_bot (Subgroup.eq_bot_of_card_eq _ h3)

end Quasisimple

section Families

theorem simple_of_bender {K : Type*} [Group K] (h : fusionIsBenderGroup K) : IsSimpleGroup K := by
  rcases h with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
    have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
      CFSG.BenderSuzuki.External.huppert_II_6_13 2 le_rfl (Or.inr (by rw [hcard]; omega))
        (Or.inr (by rw [hcard]; intro h3; omega))
    exact e.isSimpleGroup
  · have := CFSG.ShultStronglyClosedTI.unitaryCover_native_simple f hf
    exact e.isSimpleGroup
  · have hSz : Sz a = CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a :=
      (show CFSG.Theory.Comparator.SzModel a = Sz a by
        simp only [CFSG.Theory.Comparator.SzModel, CFSG.Theory.Comparator.SzGenerators, Sz,
          SzGenerators]).symm.trans (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup a)
    have : IsSimpleGroup ↥(CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a) :=
      (CFSG.BenderSuzuki.External.huppert_blackburn_XI_3_6 a ha).1
    exact (e.trans (MulEquiv.subgroupCongr hSz)).isSimpleGroup

end Families

section Main

variable {G : Type} [Group G] [Finite G]

theorem listedOTwo
    : ListedOTwo := by
  intro G _ _ M S K z hq hl hO
  have hnb : IsSimpleGroup ↥K → False := fun hs => hO (pCoreOf_eq_bot_of_simple hq hs)
  have hsl : ∀ {n p f : ℕ}, StatedClassicalModel ↥K .PSL n p f → False := fun h =>
    hnb (CFSG.LieType.Simplicity.fam_PSL_simplicity ↥K _ _ _ (by exact h)).2
  rcases hl with hB | hR | ⟨hA7, -⟩ | ⟨hD, -⟩ | ⟨⟨p, hp, hpL⟩, -⟩ | hF | ⟨hG4, -, -⟩
  · exact (hnb (simple_of_bender hB)).elim
  · rcases hR with ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | he | h | h
    · exact (hsl h).elim
    · exact (hnb (CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp
        ↥K _ _ _ (by exact h))).elim
    · have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
        alternatingGroup.isSimpleGroup (by simp)
      obtain ⟨e⟩ := he
      exact (hnb e.isSimpleGroup).elim
    · exact h
    · exact (hO (pCoreOf_eq_bot_of_card_center hq h.2.1)).elim
  · rcases hA7 with he | h
    · have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
        alternatingGroup.isSimpleGroup (by simp)
      obtain ⟨e⟩ := he
      exact (hnb e.isSimpleGroup).elim
    · exact (hO (pCoreOf_eq_bot_of_card_center hq h.2.1)).elim
  · rcases hD with h | he
    · exact (hsl h).elim
    · have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M11) :=
        CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
      obtain ⟨e⟩ := he
      exact (hnb e.isSimpleGroup).elim
  · exact (hsl hpL).elim
  · rcases hF with ⟨he, -⟩ | ⟨he, -⟩
    · have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
        CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
      obtain ⟨e⟩ := he
      exact (hnb e.isSimpleGroup).elim
    · have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M23) :=
        CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2
      obtain ⟨e⟩ := he
      exact (hnb e.isSimpleGroup).elim
  · exact (hsl hG4).elim

end Main

section Assembly

structure Lemma2411Inputs : Prop where
  a36 : A36CoreForSQTKCat
  a37 : A37ForSQTKCat
  a39 : A39ForSQTKCat
  list : Lemma2_3_9_7_listedW
  m22 : M22CoverCyclic

theorem lemma2_4_11_core_of_listed
    (h246 : Lemma246Chi) (h8 : Lemma2_4_8)
    (hin : Lemma2411Inputs) : Lemma2_4_11_core :=
  lemma2_4_11_core_of_inputs h246 h8 hin.a36 hin.a37 hin.a39 hin.list listedOTwo L34.l34Fact
    hin.m22

end Assembly

end CFSG.QuasithinUnique.Lin2
