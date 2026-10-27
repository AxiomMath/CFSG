module

public import CFSG.CGT.PushingUpLit.LIT.A4.Narrow
public import CFSG.CGT.PushingUpLit.LIT.A4.Embed
public import CFSG.CGT.PushingUpLit.LIT.A4.Sylow
public import CFSG.CGT.PushingUpLit.LIT.A4.T211Proof
public import CFSG.CGT.PushingUpLit.LIT.A4.L34All
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCat81E6A8Gen4

public section

namespace CFSG.CGT.PushingUpLit.A4

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
  CFSG.GH74

section Two

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {m : G}

theorem gen4_of_twoConj (c : A4Cfg G M X) (h : TwoConj M X m) :
    SectionalTwoRankLE G 4 := by
  have hSC := strongClosureTwo c h
  have hL := lemma34Two c h
  have hC := pairCent_eq_bot haradaTransfer211 hL c h hSC
  obtain ⟨ψ, hψ⟩ := exists_injective_perm_eight c h hC
  have hM : SectionalTwoRankLE ↥M 4 :=
    SectionalTwoRankLE.of_injective ψ hψ ComponentClassification.GSThmB.Cat81A8.gen4_perm8
  obtain ⟨Q, hQ⟩ := exists_sylow_le c h hSC
  have hQ4 : SectionalTwoRankLE ↥(Q : Subgroup G) 4 :=
    SectionalTwoRankLE.of_injective (Subgroup.inclusion hQ) (Subgroup.inclusion_injective hQ) hM
  exact SolK.SectionalTwoRankLE.of_sylow Q hQ4

theorem three_le_card_blocksOf {k : G} (hm : m ∈ M) (hk : k ∈ M) (h1 : conjSub m X ≠ X)
    (h2 : conjSub k X ≠ X) (h3 : conjSub m X ≠ conjSub k X) :
    3 ≤ Nat.card ↥(blocksOf M X) := by
  have h4 : ({X, conjSub m X, conjSub k X} : Set (Subgroup G)).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨X, conjSub m X, conjSub k X, h1.symm, h2.symm, h3, rfl⟩
  have hsub : ({X, conjSub m X, conjSub k X} : Set (Subgroup G)) ⊆ blocksOf M X := by
    intro Y hY
    rcases hY with rfl | rfl | rfl
    · exact ⟨1, M.one_mem, (conjSub_one _).symm⟩
    · exact ⟨m, hm, rfl⟩
    · exact ⟨k, hk, rfl⟩
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h4, ← Nat.card_coe_set_eq] at this
  exact this

end Two

@[expose] def ThreeConjExcluded : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M X : Subgroup G), A4Cfg G M X →
    3 ≤ Nat.card ↥(blocksOf M X) → False

theorem a4BlockNormalThree_of_threeExcl (h3 : ThreeConjExcluded) :
    A4BlockNormalThree := by
  intro G _ _ hs _ hC M X hM hXM hsub hX hnat huniq
  have c : A4Cfg G M X := ⟨hs, hC, hM, hXM, hsub, hX, hnat, huniq⟩
  by_cases hn : (X.subgroupOf M).Normal
  · exact Or.inl hn
  · right
    obtain ⟨m, hm, hne⟩ := c.exists_conj_ne hn
    by_cases h2 : ∀ k ∈ M, conjSub k X = X ∨ conjSub k X = conjSub m X
    · exact gen4_of_twoConj c ⟨hm, hne, h2⟩
    · push Not at h2
      obtain ⟨k, hk, hk1, hk2⟩ := h2
      exact (h3 G M X c (three_le_card_blocksOf hm hk hne hk1 hk2.symm)).elim

end CFSG.CGT.PushingUpLit.A4
