module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneStage

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem psl2_smallRootStage_of_card_sylow_eq_two {L : Subgroup G} (h : SeitzSetting G L)
    {f : ℕ} (hf : 3 ≤ f) (hL : LieModel L .PSL 2 2 f)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    {t : G} (ht : orderOf t = 2) (htC : t ∈ centralizer (L : Set G))
    {T : Subgroup G} (hTN : T ≤ normalizer (zpowers t : Set G))
    (hT : ∃ P : Sylow 2 (normalizer (zpowers t : Set G)),
      (P : Subgroup _) = T.subgroupOf (normalizer (zpowers t : Set G))) :
    SmallRootStage (zpowers t) L (T ⊓ L) T f := by
  have hR : Nat.card (zpowers t) = 2 := by rw [Nat.card_zpowers, ht]
  obtain ⟨hNC, -, -, hcent, -⟩ :=
    psl2_centralizer_root_of_card_sylow_eq_two h hf hL hS2 ht htC hTN hT
  refine SmallRootStage.of_gmsNormalRootData
    (gmsNormalRootData_of_psl2_of_card_sylow_eq_two h hf hL hS2 ht htC hTN hT) hR ?_
  rw [hNC]
  exact hcent

theorem psl2_smallRootStage
    {L : Subgroup G} (h : SeitzSetting G L) {f : ℕ} (hf : 3 ≤ f) (hL : LieModel L .PSL 2 2 f)
    {t : G} (ht : orderOf t = 2) (htC : t ∈ centralizer (L : Set G)) {T : Subgroup G}
    (hTN : T ≤ normalizer (zpowers t : Set G))
    (hT : ∃ P : Sylow 2 (normalizer (zpowers t : Set G)),
      (P : Subgroup _) = T.subgroupOf (normalizer (zpowers t : Set G))) :
    SmallRootStage (zpowers t) L (T ⊓ L) T f :=
  psl2_smallRootStage_of_card_sylow_eq_two h hf hL (rankOneKernel G L h (Or.inl ⟨f, hf, hL⟩)) ht
    htC hTN hT

end CFSG.SeitzReduction.RankOne
