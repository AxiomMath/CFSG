module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpChainBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Section

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG.EvenSporadicStandard.HSStd CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Card

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_zpowers_involution {t x : G} (ht : orderOf t = 2) (hx : x ∈ zpowers t) :
    x = 1 ∨ x = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  have h := zpow_mod_orderOf t k
  rw [ht] at h
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [← h]
    have : k % ((2 : ℕ) : ℤ) = 0 := by exact_mod_cast h0
    rw [this, zpow_zero]
  · right
    rw [← h]
    have : k % ((2 : ℕ) : ℤ) = 1 := by exact_mod_cast h1
    rw [this, zpow_one]

omit [Finite G] in
theorem card_sup_zpowers_involution (L : Subgroup G) {t : G} (ht : t ∈ centralizer (L : Set G))
    (ht2 : orderOf t = 2) (htL : t ∉ L) : Nat.card ↥(L ⊔ zpowers t) = 2 * Nat.card L := by
  set J := L ⊔ zpowers t with hJ
  have hLJ : L ≤ J := le_sup_left
  have hTJ : zpowers t ≤ J := le_sup_right
  have hJc : J ≤ centralizer ({t} : Set G) := by
    refine sup_le (fun l hl => ?_) ?_
    · rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.1 ht l hl
    · rw [zpowers_le]
      exact mem_centralizer_singleton_iff.2 rfl
  set A := L.subgroupOf J with hA
  set B := (zpowers t).subgroupOf J with hB
  have hBn : B.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hB, mem_subgroupOf] at hn ⊢
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hn
    have hgt : Commute (g : G) t := mem_centralizer_singleton_iff.1 (hJc g.2)
    have : (g : G) * (n : G) * (g : G)⁻¹ = (n : G) := by
      rw [← hk, (hgt.zpow_right k).eq]
      simp
    show (g : G) * (n : G) * (g : G)⁻¹ ∈ zpowers t
    rw [this]
    exact hn
  have hsup : A ⊔ B = ⊤ := by
    rw [hA, hB, ← subgroupOf_sup hLJ hTJ, ← hJ, subgroupOf_self]
  have h1 : B.relIndex (A ⊔ B) = B.relIndex A := Subgroup.relIndex_sup_right A B
  rw [hsup, Subgroup.relIndex_top_right] at h1
  have h2 : B.subgroupOf A = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [mem_subgroupOf, hB, mem_subgroupOf] at hx
    have hxL : ((x : J) : G) ∈ L := x.2
    rcases mem_zpowers_involution ht2 hx with h0 | h0
    · rw [mem_bot]
      apply Subtype.ext
      apply Subtype.ext
      exact h0
    · exact absurd (h0 ▸ hxL) htL
  rw [Subgroup.relIndex, h2, Subgroup.index_bot] at h1
  have h3 : Nat.card B = 2 := by
    rw [← ht2, ← Nat.card_zpowers]
    exact Nat.card_congr (subgroupOfEquivOfLe hTJ).toEquiv
  have h4 : Nat.card A = Nat.card L := Nat.card_congr (subgroupOfEquivOfLe hLJ).toEquiv
  have h5 := Subgroup.card_mul_index B
  rw [h1, h3, h4] at h5
  exact h5.symm

omit [Finite G] in
theorem card_centralizer_involution (L : Subgroup G) {t : G} (ht : t ∈ centralizer (L : Set G))
    (ht2 : orderOf t = 2) (htL : t ∉ L)
    (hidx : (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) = 2) :
    Nat.card (centralizer ({t} : Set G)) = 4 * Nat.card L := by
  have hJc : L ⊔ zpowers t ≤ centralizer ({t} : Set G) := by
    refine sup_le (fun l hl => ?_) ?_
    · rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.1 ht l hl
    · rw [zpowers_le]
      exact mem_centralizer_singleton_iff.2 rfl
  have h1 := Subgroup.card_mul_index ((L ⊔ zpowers t).subgroupOf (centralizer ({t} : Set G)))
  have h2 : Nat.card ↥((L ⊔ zpowers t).subgroupOf (centralizer ({t} : Set G))) =
      Nat.card ↥(L ⊔ zpowers t) := Nat.card_congr (subgroupOfEquivOfLe hJc).toEquiv
  have h3 : ((L ⊔ zpowers t).subgroupOf (centralizer ({t} : Set G))).index = 2 := hidx
  rw [h2, h3, card_sup_zpowers_involution L ht ht2 htL] at h1
  omega

end Card

section Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {S : Subgroup G} {z n v s : G}

theorem pumpCtx_of_setup (h : HSOuterSetup G L t S z n v s) : PumpCtx G where
  simple := h.setting.1.simple
  nonabelian := h.setting.1.nonabelian
  kProper := h.setting.1.kProper
  balanced x hx := h.setting.1.oddCore x hx

theorem card_L_of_setup (h : HSOuterSetup G L t S z n v s) :
    Nat.card L = 44352000 := by
  obtain ⟨e₀⟩ := h.setting.2.1
  have e : ↥L ≃* NativeSporadic.HS := e₀
  exact (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.HS.card_HS

theorem dvd_card_of_setup (h : HSOuterSetup G L t S z n v s) :
    44352000 ∣ Nat.card G := by
  rw [← card_L_of_setup h]
  exact Subgroup.card_subgroup_dvd_card L

theorem t_not_mem_of_setup (h : HSOuterSetup G L t S z n v s) :
    t ∉ L := by
  intro htL
  have hc : center ↥L = ⊥ := center_eq_bot_of_isSporadic_hs h.setting.2.1
  have hz : (⟨t, htL⟩ : ↥L) ∈ center ↥L := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.1 h.t_mem g g.2)
  rw [hc, mem_bot] at hz
  exact h.t_ne_one (congrArg Subtype.val hz)

theorem card_centralizer_of_setup
    (h : HSOuterSetup G L t S z n v s) :
    Nat.card (centralizer ({t} : Set G)) = 177408000 := by
  rw [card_centralizer_involution L h.t_mem h.t_two (t_not_mem_of_setup h) h.index,
    card_L_of_setup h]

theorem exists_involution_of_setup
    (h : HSOuterSetup G L t S z n v s) :
    ∃ t : G, orderOf t = 2 ∧ Nat.card (centralizer ({t} : Set G)) = 177408000 :=
  ⟨t, h.t_two, card_centralizer_of_setup h⟩

end Setup

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
