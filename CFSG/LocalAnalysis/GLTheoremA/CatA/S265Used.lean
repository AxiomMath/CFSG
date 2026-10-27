module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Sub
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs103
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Transport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

section Used

variable {G : Type} [Group G] [Finite G]

theorem i265UsedAt_of_fact (hF : FactU) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : ∀ y : G, y ≠ 1 → CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({y} : Set G))) :
    I265UsedAt G p := by
  classical
  intro B x L b hS hchev hG hb hbx hR hTD hI hnI
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hBel, hBcard, -, -, -⟩ : IsElemAbelian p B ∧ Nat.card ↥B = p ^ GLATwoLocalRank p G ∧
      ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set G) := IsSStarMax.bmax hS
  have hess := IsSStarMax.essential hS
  have hxB : x ∈ B := hess.1
  have hx1 : x ≠ 1 := hess.2.1
  have hLc : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L := IsSStarMax.component hS
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := IsSStarMax.normalizes hS
  have hcyc : CycModSylow p L := IsSStarMax.cycMod hS
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hLc.1
  obtain ⟨E₀, hE₀B, hE₀el, hE₀c, hE₀l⟩ := hG
  rw [closureIn_eq_self_of_le hBN] at hE₀l
  by_cases h3 : Nat.card B = p ^ 3
  ·
    left
    have hEB : E₀ = B := Subgroup.eq_of_le_of_card_ge hE₀B (by rw [hE₀c, h3])
    refine ⟨E₀, hE₀B, hE₀el, hE₀c, ?_, hE₀l⟩
    rw [hEB]
    refine (Subgroup.closure_le _).2 ?_
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hb
    · exact hxB
  have h4 : p ^ 4 ≤ Nat.card B := by
    have h1 : p ^ 3 ≤ Nat.card B := hE₀c ▸ Subgroup.card_le_of_le hE₀B
    rw [hBcard] at h1 h3 ⊢
    have h2 : 3 ≤ GLATwoLocalRank p G := (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
    have h5 : GLATwoLocalRank p G ≠ 3 := fun h => h3 (by rw [h])
    exact Nat.pow_le_pow_right hp.pos (by omega)
  obtain ⟨T, hTC, hT2, hBT, hTT, hT0⟩ :=
    exists_two_group_comm_eq hp hp2 (isPGroup_of_isElemAbelian hBel) hess
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := hTC.trans (S171.cx_le_normalizer hp hp2 hS)
  set H : Subgroup G := L ⊔ B ⊔ T with hH
  have hLH : L ≤ H := le_sup_left.trans le_sup_left
  have hBH : B ≤ H := le_sup_right.trans le_sup_left
  have hTH : T ≤ H := le_sup_right
  have hHN : H ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer hBN) hTN
  have hBx : B ≤ Subgroup.centralizer ({x} : Set G) := fun c hc =>
    Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hBel hc hxB)
  have hHx : H ≤ Subgroup.centralizer ({x} : Set G) := sup_le (sup_le hLx hBx) hTC
  have hxH : x ∈ H := hBH hxB
  have hbH : b ∈ H := hBH hb
  have hxL : x ∈ centModSubgroup p L := by
    refine centMod_iff.1 (centMod_of_mem_centralizer ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.1 (hLx hl)
  have hcm : ∀ c ∈ B, CentMod p L c ↔ c ∈ Subgroup.zpowers x :=
    centMod_iff_mem_zpowers hp hBel hxB hx1 hxL hcyc
  have hBHel : IsElemAbelian p (B.subgroupOf H) := isElemAbelian_subgroupOf' H hBel
  have hcomp : GLAPComponent p (⊤ : Subgroup ↥H) (L.subgroupOf H) := by
    have h1 := glaPComponent_of_le hp hLc hLH hHx
    have h2 := I2015.glaPComponent_subgroupOf (le_refl H) h1
    rwa [Subgroup.subgroupOf_self] at h2
  have hRH : R2Prop p (⟨b, hbH⟩ : ↥H) (L.subgroupOf H) := by
    rcases hR with hF' | ⟨hp3, hT3, hNI⟩
    · exact Or.inl (fieldOn_subgroupOf hp hLH hHN hbH hF')
    · refine Or.inr ⟨hp3, (T156.isTD4_congr hp3 (eL hp hLH)).2 hT3, mem_normalizer_subgroupOf hLH hHN _, ?_⟩
      intro hI'
      apply hNI.2
      have hN3 : ¬ 3 ∣ Nat.card (H.subtype : ↥H →* G).ker := T156.not_dvd_card_ker_subtype Nat.prime_three H
      have h2 := T156.inducesInnerMod_map Nat.prime_three H.subtype hN3 hI'
      rwa [Subgroup.map_subgroupOf_eq_of_le hLH] at h2
  have hg2 : p = 3 → IsTD4 3 (L.subgroupOf H) →
      centCard2 3 (L.subgroupOf H) (⟨b, hbH⟩ : ↥H) = Nat.sqrt (card2 3 (L.subgroupOf H)) := by
    intro h3' hT'
    have hT3 : IsTD4 3 L := (T156.isTD4_congr h3' (eL hp hLH)).1 hT'
    have key := hTD h3' hT3
    subst h3'
    rw [centCard2_subgroupOf hp hLH hHN, card2_subgroupOf hp hLH]
    exact key
  have hcfg : UCfg p (L.subgroupOf H) (B.subgroupOf H) (T.subgroupOf H) ⟨x, hxH⟩ ⟨b, hbH⟩ :=
    { prime := hp
      odd := hp2
      kgroup := CFSG.Open.IsKGroup.of_le (hK x hx1) hHx
      comp := hcomp
      normal := normal_subgroupOf hLH hHN
      chev := T156.isChevSimple_congr (T156.psimpleIso (eL hp hLH).symm) hchev
      gen := sup3_subgroupOf rfl
      elem := hBHel
      two := isPGroup_subgroupOf' hT2 hTH
      bnorm := le_normalizer_subgroupOf hBH hTH hBT
      ne := comm_subgroupOf_ne_bot hBH hTH (by rw [hTT]; exact hT0)
      rank := by
        refine (Nat.pow_le_pow_right hp.pos (twoLocalRank_subgroup hp H)).trans ?_
        rw [card_subgroupOf' hBH, hBcard]
      big := by rw [card_subgroupOf' hBH]; exact h4
      cyc := cycModSylow_subgroupOf hp hLH hHN hcyc
      xB := Subgroup.mem_subgroupOf.2 hxB
      x1 := fun h => hx1 (congrArg Subtype.val h)
      xcen := fun g => Subtype.ext (by
        have := Subgroup.mem_centralizer_singleton_iff.1 (hHx g.2)
        simpa using this)
      centB := fun c hc => by
        rw [centMod_subgroupOf_iff hp hLH hHN c, mem_zpowers_subgroupOf_iff]
        exact hcm (c : G) (Subgroup.mem_subgroupOf.1 hc)
      hb := Subgroup.mem_subgroupOf.2 hb
      hbx := fun h => hbx ((mem_zpowers_subgroupOf_iff _ _).1 h)
      prop := hRH
      g2 := hg2
      ipart := (layer_cx_subgroupOf_ne_bot_iff hp hLH hbH).2 hI
      noninn := fun h => hnI (innDiagOn_of_subgroupOf hp hLH hHN hBH h)
      gstar := ⟨E₀.subgroupOf H, Subgroup.subgroupOf_mono H hE₀B, isElemAbelian_subgroupOf' H hE₀el,
        by rw [card_subgroupOf' (hE₀B.trans hBH), hE₀c],
        (layer_cs_subgroupOf_ne_bot_iff hp hLH (hE₀B.trans hBH)).2 hE₀l⟩ }
  rcases hF p ↥H (L.subgroupOf H) (B.subgroupOf H) (T.subgroupOf H) ⟨x, hxH⟩ ⟨b, hbH⟩ hcfg with
    ⟨E, hEB, hEel, hEcard, hDE, hElay⟩ | ⟨hp3, hU, hFi⟩
  · left
    refine ⟨E.map H.subtype, ?_, ?_, ?_, ?_, ?_⟩
    · exact (Subgroup.map_mono hEB).trans (Subgroup.map_subgroupOf_eq_of_le hBH).le
    · exact CFSG.Open.IsElemAbelian.map hEel H.subtype
    · rw [Subgroup.card_map_of_injective H.subtype_injective, hEcard]
    · refine (Subgroup.closure_le _).2 ?_
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      have hmem : ∀ z : ↥H, z ∈ Dgrp (⟨b, hbH⟩ : ↥H) (⟨x, hxH⟩ : ↥H) → (z : G) ∈ E.map H.subtype :=
        fun z hz => Subgroup.mem_map_of_mem _ (hDE hz)
      rcases hy with rfl | rfl
      · exact hmem ⟨y, hbH⟩ (Subgroup.subset_closure (by simp))
      · exact hmem ⟨y, hxH⟩ (Subgroup.subset_closure (by simp))
    · exact (layer_cs_map_ne_bot_iff hp hLH E).2 hElay
  · right
    subst hp3
    exact ⟨rfl, (T156.psimple3_congr rfl (eL hp hLH) _).1 hU, fieldOn_of_subgroupOf hp hLH hHN hbH hFi⟩

end Used

end CFSG.LocalAnalysis.GLTheoremA.S265

end
