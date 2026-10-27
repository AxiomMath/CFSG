module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Thm3One
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Thm5

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem5
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix

variable {G : Type} [Group G] [Finite G]

theorem HasFourGroup.of_bar {Q T : Subgroup G} (hT2 : IsPGroup 2 T)
    (h : HasFourGroup (bar Q T)) : HasFourGroup T := by
  obtain ⟨E, hET, hE, hE4⟩ := h
  set F₀ : Subgroup (normalizer (Q : Set G)) :=
    E.comap (toBar Q) ⊓ T.subgroupOf (normalizer (Q : Set G))
  have hinj : Set.InjOn (toBar Q) (F₀ : Set (normalizer (Q : Set G))) := fun u hu v hv huv =>
    toBar_injOn_of_isPGroup hT2 (mem_subgroupOf.mp (mem_inf.mp hu).2)
      (mem_subgroupOf.mp (mem_inf.mp hv).2) huv
  have himage : F₀.map (toBar Q) = E := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (mem_inf.mp hx).1
    · intro e he
      obtain ⟨x, hxT, hx⟩ := (mem_bar_iff Q T e).mp (hET he)
      exact ⟨x, mem_inf.mpr ⟨by rw [mem_comap, hx]; exact he, hxT⟩, hx⟩
  refine ⟨F₀.map (normalizer (Q : Set G)).subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_inf.mp hx).2
  · rintro _ ⟨x, hx, rfl⟩
    have h1 : toBar Q (x ^ 2) = toBar Q 1 := by
      rw [map_pow, map_one]
      exact hE _ (mem_inf.mp hx).1
    have h2 := toBar_injOn_of_isPGroup hT2 (mem_subgroupOf.mp (pow_mem (mem_inf.mp hx).2 2))
      (by simp) h1
    simpa using congrArg Subtype.val h2
  · rw [card_map_of_injective (normalizer (Q : Set G)).subtype_injective, ← hE4, ← himage]
    symm
    rw [← SetLike.coe_sort_coe, coe_map, Nat.card_image_of_injOn hinj]
    rfl

theorem pRank_bar_le_one {Q T : Subgroup G} (hT2 : IsPGroup 2 T) (h4 : ¬ HasFourGroup T) :
    CFSG.Open.pRank 2 (bar Q T) ≤ 1 := by
  by_contra h
  exact h4 (HasFourGroup.of_bar (Q := Q) hT2 (hasFourGroup_of_one_lt_pRank (by omega)))

namespace MainSetting

variable {Q : Subgroup G} (hS : MainSetting Q)
include hS

theorem not_hasFourGroup_inf_normalizer (hC : linkedClass Q = {Q}) {g : G}
    (hg : g ∉ normalizer (Q : Set G)) :
    ¬ HasFourGroup (Q ⊓ normalizer (rightConjugate Q g : Set G)) := by
  intro h4
  have hle : twoPrimeLayerIn (rightConjugate Q g) ≤ normalizer (rightConjugate Q 1 : Set G) := by
    have hI := hS.caseI 1 g
    rw [rightConjugate_one] at hI ⊢
    exact hI h4
  have hL := hS.linked_of_le hle
  rw [rightConjugate_one] at hL
  have hmem : rightConjugate Q g ∈ linkedClass Q := ⟨⟨g, rfl⟩, hL.symm⟩
  rw [hC, Set.mem_singleton_iff, rightConjugate_eq_self_iff] at hmem
  exact hg hmem

theorem not_le_normalizer_bar (hC : linkedClass Q = {Q}) {g : G}
    (hg : g ∉ normalizer (Q : Set G)) {T : Subgroup G} (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hTQg : T ≤ rightConjugate Q g) (hTH : T ≤ normalizer (Q : Set G)) :
    ¬ bar Q Q ≤ normalizer (bar Q T : Set (Bar Q)) := by
  intro h
  rw [normalizer_bar hT2 hTH] at h
  have hcov : Q ≤ (Q ⊓ normalizer (T : Set G)) ⊔ oddCoreIn Q := by
    intro q hq
    obtain ⟨n, hnT, hn⟩ :=
      (mem_bar_iff Q _ _).mp (h (toBar_mem_bar Q (h := ⟨q, le_normalizer hq⟩) hq))
    have hO : (n : G)⁻¹ * q ∈ oddCoreIn Q := by
      have h1 : n⁻¹ * ⟨q, le_normalizer hq⟩ ∈ coreIn Q := QuotientGroup.eq.mp hn
      exact h1
    have hnQ : (n : G) ∈ Q := by
      have : (n : G) = q * ((n : G)⁻¹ * q)⁻¹ := by group
      rw [this]
      exact mul_mem hq (inv_mem (oddCoreIn_le Q hO))
    have : q = n * ((n : G)⁻¹ * q) := by group
    rw [this]
    exact mul_mem (mem_sup_left (mem_inf.mpr ⟨hnQ, hnT⟩)) (mem_sup_right hO)
  have hQO : Q ≤ normalizer (oddCoreIn Q : Set G) := normalIn_le_normalizer (oddCoreIn_normalIn Q)
  obtain ⟨E, hEK, hE, hE4⟩ := hS.four
  have hEQ : E ≤ Q := hEK.trans (twoPrimeLayerIn_le Q)
  have h4 := HasFourGroup.of_le_sup (odd_card_oddCoreIn Q) (inf_le_left.trans hQO)
    (hEQ.trans hQO) (hEQ.trans hcov) hE hE4
  have hTe : Even (Nat.card T) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp hT2)
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hT1 (Subgroup.eq_bot_of_card_eq T (by rw [hn, pow_zero]))
    rw [hn]
    exact (Nat.even_pow' hn0).mpr even_two
  have hNT : normalizer (T : Set G) ≤ normalizer (rightConjugate Q g : Set G) :=
    normalizer_le_of_even (rightConjugate_tightlyEmbedded Q hS.tight g) hTQg hTe
  exact hS.not_hasFourGroup_inf_normalizer hC hg (h4.mono (inf_le_inf_left _ hNT))

theorem thm3RankOne_of_linkedClass_eq (hC : linkedClass Q = {Q}) {g : G}
    (hg : g ∉ normalizer (Q : Set G)) {T : Subgroup G}
    (hT : IsSylowOf 2 T (rightConjugate Q g ⊓ normalizer (Q : Set G))) (hT1 : T ≠ ⊥) :
    ∃ S : Subgroup G, IsSylowOf 2 S (Q ⊔ T) ∧ T ≤ S ∧ T ⊓ Q = ⊥ ∧
      Thm3RankOne (bar Q Q) (bar Q T) (bar Q S) := by
  obtain ⟨S, hS', hTS, hbot, h⟩ := exists_hyp3_bar hS.tight hg hT hT1
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hTH : T ≤ normalizer (Q : Set G) := hT.le.trans inf_le_right
  have h4 : ¬ HasFourGroup T := fun h4 =>
    hS.not_hasFourGroup_of_linkedClass_eq hC hg (h4.mono hT.le)
  rcases theorem_3_rankOne h (pRank_bar_le_one hT2 h4) with h1 | h2
  · exact ⟨S, hS', hTS, hbot, h1⟩
  · exact absurd (le_sup_left.trans h2)
      (hS.not_le_normalizer_bar hC hg hT2 hT1 (hT.le.trans inf_le_left) hTH)

end MainSetting

end CFSG.ComponentClassification.Asc75T4
