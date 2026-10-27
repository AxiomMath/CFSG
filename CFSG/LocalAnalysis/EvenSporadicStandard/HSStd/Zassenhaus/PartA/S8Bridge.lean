module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG CFSG.LocalCores
open scoped commutatorElement

theorem gw_isQuasisimple_iff {Q : Type*} [Group Q] :
    CFSG.GorensteinWalter.IsQuasisimple Q ↔ CFSG.IsQuasisimple Q := by
  constructor
  · rintro ⟨hnt, hp, hs⟩
    refine ⟨Group.isPerfect_def.mpr hp, hs, ?_⟩
    by_contra h
    push Not at h
    have hle : commutator Q ≤ center Q := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      have h1 : ⁅(a : Q ⧸ center Q), (b : Q ⧸ center Q)⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.2 (h _ _)
      have h2 : (QuotientGroup.mk' (center Q)) ⁅a, b⁆ = 1 := by
        rw [map_commutatorElement]; exact h1
      exact (QuotientGroup.eq_one_iff _).1 h2
    rw [hp] at hle
    obtain ⟨x, hx⟩ := exists_ne (1 : Q)
    apply hx
    have hcen : ∀ y : Q, x * y = y * x := fun y =>
      (Subgroup.mem_center_iff.1 (hle (mem_top x)) y).symm
    have hab : ∀ a b : Q, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.1 (hle (mem_top a)) b).symm
    have : commutator Q = ⊥ := by
      rw [_root_.commutator_def, eq_bot_iff, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hab a b
    rw [hp] at this
    exact (Subgroup.mem_bot.1 (this ▸ mem_top x))
  · intro h
    exact ⟨isQuasisimple_nontrivial h, Group.isPerfect_def.mp h.1, h.2.1⟩

variable {G : Type*} [Group G]

theorem gw_isComponentOf_iff {X H : Subgroup G} (hX : X ≤ H) :
    CFSG.GorensteinWalter.IsComponentOf X H ↔ CFSG.IsComponent (X.subgroupOf H) := by
  constructor
  · rintro ⟨-, hsn, hq⟩
    exact ⟨isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hX).symm
      (gw_isQuasisimple_iff.1 hq), hsn⟩
  · rintro ⟨hq, hsn⟩
    exact ⟨hX, hsn, gw_isQuasisimple_iff.2
      (isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hX) hq)⟩

theorem componentLayerOf_eq (H : Subgroup G) :
    CFSG.GorensteinWalter.componentLayerOf H = (layer ↥H).map H.subtype := by
  apply le_antisymm
  · refine sSup_le fun X hX => ?_
    have hXH : X ≤ H := hX.1
    have hc := (gw_isComponentOf_iff hXH).1 hX
    rw [← Subgroup.map_subgroupOf_eq_of_le hXH]
    exact Subgroup.map_mono (component_le_layer hc)
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun Y hY y hy => ?_
    have hXH : Y.map H.subtype ≤ H := Subgroup.map_subtype_le Y
    have hcomp : CFSG.GorensteinWalter.IsComponentOf (Y.map H.subtype) H := by
      have e : (Y.map H.subtype).subgroupOf H = Y :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective Y
      rw [gw_isComponentOf_iff hXH, e]
      exact hY
    exact (le_sSup hcomp : Y.map H.subtype ≤ _) ⟨y, hy, rfl⟩

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
