module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiRegularStab
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiRegularEight
public import CFSG.LocalAnalysis.SeitzReduction.RankOneOddStabilizerKProper

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.Blueprint

namespace SzStart

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem normalizer_szA_ne_top_of_card_sylow
    (h : SzStart G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    normalizer (szA L T t : Set G) ≠ ⊤ := by
  intro htop
  have hnorm : (szA L T t).Normal := normalizer_eq_top_iff.mp htop
  have : IsSimpleGroup G := h.setting.1
  rcases Subgroup.Normal.eq_bot_or_eq_top (szA L T t) with hbot | htop'
  · have ht := mem_szA_right L T t
    rw [hbot, mem_bot] at ht
    have h2 := h.inv
    rw [ht, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  · obtain ⟨x, y, hxy⟩ := h.setting.2.1
    obtain ⟨-, -, hcomm⟩ := h.szA_facts_of_card_sylow hS2
    exact hxy (hcomm x (htop' ▸ mem_top x) y (htop' ▸ mem_top y))

section RHKS

theorem exists_regular_elementary_of_card_sylow (h : SzStart G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hT : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T) :
    ∃ E : Subgroup (Equiv.Perm (gmsRootConjugates (szA L T t) (zpowers t))),
      E ≤ (gmsRootConjugateAction (szA L T t) (zpowers t)).range ∧
      (E.subgroupOf (gmsRootConjugateAction (szA L T t) (zpowers t)).range).Normal ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 2 = 1) ∧ Nat.card E = 2 ^ f ∧
      ∀ Q Z, ∃! e : E, (e : Equiv.Perm (gmsRootConjugates (szA L T t) (zpowers t))) Q = Z := by
  obtain ⟨-, hcard, -, h2⟩ := h.partition_of_card_sylow hS2 hT
  obtain ⟨hodd, hdvd⟩ := h.stabilizer_odd_dvd_of_card_sylow hS2 hT
  obtain ⟨a, -, hfa, -⟩ := exists_benderType_of_lieModel_twistedB2 h.model
  have hΩ : Nat.card (gmsRootConjugates (szA L T t) (zpowers t)) = 2 ^ f := by
    rw [Nat.card_coe_set_eq]
    exact hcard
  rcases odd_stabilizer_two_transitive_kProper_of_dvd h.setting.2.2.1
      (h.normalizer_szA_ne_top_of_card_sylow hS2)
      (gmsRootConjugateAction (szA L T t) (zpowers t)) _ le_rfl h2 (by omega : 1 ≤ f) hΩ
      ⟨zpowers t, zpowers_mem_gmsRootConjugates_szA L T t⟩ hodd hdvd with
    hE | ⟨hf3, -, h168, hs, -⟩
  · exact hE
  · exact (h.false_of_card_range_eq_168_of_card_sylow hS2 hT hf3 h168 hs).elim

end RHKS

section Main

theorem exists_regular_elementary (h : SzStart G L f t T) :
    ∃ E : Subgroup (Equiv.Perm (gmsRootConjugates (szA L T t) (zpowers t))),
      E ≤ (gmsRootConjugateAction (szA L T t) (zpowers t)).range ∧
      (E.subgroupOf (gmsRootConjugateAction (szA L T t) (zpowers t)).range).Normal ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 2 = 1) ∧ Nat.card E = 2 ^ f ∧
      ∀ Q Z, ∃! e : E, (e : Equiv.Perm (gmsRootConjugates (szA L T t) (zpowers t))) Q = Z :=
  h.exists_regular_elementary_of_card_sylow h.card_sylow h.not_sylow

end Main

end SzStart

end CFSG.SeitzReduction.RankOne
