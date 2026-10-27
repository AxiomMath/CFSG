module

import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Tower

open CFSG.Open Subgroup

variable {A : Type} [Group A]

@[expose] def preHatOf (P : Subgroup A) (U : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)) : Subgroup A :=
  (U.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥P))).map P.subtype

theorem preHatOf_le (P : Subgroup A) (U : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)) :
    preHatOf P U ≤ P :=
  Subgroup.map_subtype_le _

theorem mem_preHatOf_iff {P : Subgroup A} {U : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)} {x : A} :
    x ∈ preHatOf P U ↔ ∃ hx : x ∈ P, QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨x, hx⟩ ∈ U := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem hatOf_preHatOf (P : Subgroup A) (U : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)) :
    hatOf P (preHatOf P U) = U := by
  unfold hatOf preHatOf
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) U

theorem hatOf_mono {P J J' : Subgroup A} (h : J ≤ J') : hatOf P J ≤ hatOf P J' :=
  Subgroup.map_mono fun _ hx => h hx

theorem pCoreOf_le_preHatOf (P : Subgroup A) (U : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)) :
    pCoreOf 2 P ≤ preHatOf P U := by
  intro x hx
  have hxP : x ∈ P := CFSG.openPCoreOf_le 2 P hx
  rw [mem_preHatOf_iff]
  refine ⟨hxP, ?_⟩
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨x, hxP⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).2 ((CFSG.mem_openPCoreOf_iff ⟨x, hxP⟩).1 hx)
  rw [h1]
  exact U.one_mem

theorem hatOf_normal {P J J' : Subgroup A} (hJJ' : J ≤ J') (hn : (J.subgroupOf J').Normal) :
    ((hatOf P J).subgroupOf (hatOf P J')).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (hatOf_mono hJJ')]
  rintro _ _ ⟨j, hj, rfl⟩ ⟨j', hj', rfl⟩
  refine ⟨j' * j * j'⁻¹, ?_, by simp⟩
  exact (Subgroup.normal_subgroupOf_iff hJJ').1 hn (j : A) (j' : A) hj hj'

theorem hatOf_le_normalizer {P T J : Subgroup A} (hTP : T ≤ P) (h : J ≤ normalizer (T : Set A)) :
    hatOf P J ≤ normalizer ((hatOf P T : Subgroup _) : Set _) := by
  rintro _ ⟨g, hg, rfl⟩
  have hgN : g ∈ normalizer ((T.subgroupOf P : Subgroup ↥P) : Set ↥P) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hTP]
    exact h hg
  exact Subgroup.le_normalizer_map (H := T.subgroupOf P) (QuotientGroup.mk' (CFSG.pCore 2 ↥P))
    (Subgroup.mem_map_of_mem _ hgN)

theorem card_hatOf_mul [Finite A] {P J : Subgroup A} (hJP : J ≤ P) (hQJ : pCoreOf 2 P ≤ J) :
    Nat.card (hatOf P J) * Nat.card (CFSG.pCore 2 ↥P) = Nat.card J := by
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥P)).ker ≤ J.subgroupOf P := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact hQJ ((CFSG.mem_openPCoreOf_iff x).2 hx)
  have h1 := Subgroup.relIndex_mul_card (QuotientGroup.mk' (CFSG.pCore 2 ↥P)).ker
    (J.subgroupOf P)
  rw [Subgroup.relIndex_ker, inf_eq_left.2 hker, QuotientGroup.ker_mk'] at h1
  have h2 : Nat.card (J.subgroupOf P) = Nat.card J :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJP).toEquiv
  rw [h2] at h1
  exact h1

theorem card_hatOf_le_two_mul [Finite A] {P T J : Subgroup A} (hTP : T ≤ P) (hJP : J ≤ P)
    (hQT : pCoreOf 2 P ≤ T) (hQJ : pCoreOf 2 P ≤ J) (h : Nat.card T ≤ 2 * Nat.card J) :
    Nat.card (hatOf P T) ≤ 2 * Nat.card (hatOf P J) := by
  have h1 := card_hatOf_mul hTP hQT
  have h2 := card_hatOf_mul hJP hQJ
  have hpos : 0 < Nat.card (CFSG.pCore 2 ↥P) := Nat.card_pos
  rw [← h1, ← h2] at h
  have h3 : Nat.card (hatOf P T) * Nat.card (CFSG.pCore 2 ↥P) ≤
      (2 * Nat.card (hatOf P J)) * Nat.card (CFSG.pCore 2 ↥P) := by
    calc Nat.card (hatOf P T) * Nat.card (CFSG.pCore 2 ↥P)
        ≤ 2 * (Nat.card (hatOf P J) * Nat.card (CFSG.pCore 2 ↥P)) := h
      _ = (2 * Nat.card (hatOf P J)) * Nat.card (CFSG.pCore 2 ↥P) := by ring
  exact Nat.le_of_mul_le_mul_right h3 hpos

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Tower
