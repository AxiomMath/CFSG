module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Props
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Swap

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG CFSG.EvenSporadicStandard.SolomonRed
open scoped commutatorElement

theorem normalClosureOf_eq_of_normal {G : Type*} [Group G] {L : Subgroup G} (hL : L.Normal) :
    normalClosureOf L = L := by
  haveI : L.Normal := hL
  unfold normalClosureOf
  exact Subgroup.normalClosure_eq_self L

theorem normalClosureOf_eq_of_le_simple {G : Type*} [Group G] {L S : Subgroup G} (hS : S.Normal)
    (hSs : IsSimpleGroup ↥S) (hLS : L ≤ S) (hL1 : L ≠ ⊥) : normalClosureOf L = S := by
  haveI : S.Normal := hS
  let N : Subgroup G := Subgroup.normalClosure (L : Set G)
  have hN_le_S : N ≤ S := Subgroup.normalClosure_le_normal hLS
  have hNn : N.Normal := Subgroup.normalClosure_normal
  haveI hNsub : (N.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff hN_le_S).2 fun h k hh _ => hNn.conj_mem h hh k
  have hNne : N ≠ ⊥ := by
    intro hbot
    apply hL1
    rw [eq_bot_iff]
    intro x hx
    have hxN : x ∈ N := Subgroup.le_normalClosure hx
    rw [hbot, mem_bot] at hxN
    simpa using hxN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf S) with hbot | htop
  · exfalso
    apply hNne
    rw [eq_bot_iff]
    intro x hx
    have hxS : x ∈ S := hN_le_S hx
    have hx' : (⟨x, hxS⟩ : ↥S) ∈ N.subgroupOf S := hx
    rw [hbot, mem_bot] at hx'
    simpa using congrArg Subtype.val hx'
  · unfold normalClosureOf
    refine le_antisymm hN_le_S fun s hs => ?_
    have hs' : (⟨s, hs⟩ : ↥S) ∈ N.subgroupOf S := by rw [htop]; trivial
    exact (Subgroup.mem_subgroupOf).1 hs'

theorem normalClosureOf_eq_layer {K : Type*} [Group K] [Finite K] {z : K} {B S₁ S₂ : Subgroup K}
    (h : Setting K z B) (hs : SwapData K z B S₁ S₂) : normalClosureOf B = layer K := by
  let N : Subgroup K := Subgroup.normalClosure (B : Set K)
  have hNn : N.Normal := Subgroup.normalClosure_normal
  have hB_le_N : B ≤ N := Subgroup.le_normalClosure
  have hS₂_le_layer : S₂ ≤ layer K := by rw [hs.layer_eq]; exact le_sup_right
  have hB_le_layer : B ≤ layer K := by
    rw [← hs.inf_eq]; exact inf_le_left
  haveI : (layer K).Characteristic := CFSG.LocalCores.layer_characteristic
  have hN_le_layer : N ≤ layer K := Subgroup.normalClosure_le_normal hB_le_layer
  have hS₁_le_N : S₁ ≤ N := by
    rw [← Subgroup.isPerfect_iff.mp hs.comp.1.1, Subgroup.commutator_le]
    intro u hu s hs1
    set d : K := s * (z * s * z⁻¹) with hd
    have hd_layer : d ∈ layer K := by
      rw [hd]
      exact (layer K).mul_mem (hs.le_layer hs1) (hS₂_le_layer (hs.conj_mem_S₂ hs1))
    have hd_cent : d ∈ centralizer ({z} : Set K) := by
      rw [hd]
      exact mem_centralizer_singleton_iff.2
        (swap_fixed h.z_sq hs.commute hs.conj_eq hs1).symm
    have hd_B : d ∈ B := by
      rw [← hs.inf_eq]
      exact ⟨hd_layer, hd_cent⟩
    have hdN : d ∈ N := hB_le_N hd_B
    have hcommN : u * d * u⁻¹ * d⁻¹ ∈ N :=
      N.mul_mem (hNn.conj_mem d hdN u) (N.inv_mem hdN)
    have hXu : (z * s * z⁻¹) * u⁻¹ = u⁻¹ * (z * s * z⁻¹) := by
      have h1 : u * (z * s * z⁻¹) = (z * s * z⁻¹) * u :=
        hs.commute u hu (z * s * z⁻¹) (hs.conj_mem_S₂ hs1)
      calc (z * s * z⁻¹) * u⁻¹
          = u⁻¹ * (u * (z * s * z⁻¹)) * u⁻¹ := by group
        _ = u⁻¹ * ((z * s * z⁻¹) * u) * u⁻¹ := by rw [h1]
        _ = u⁻¹ * (z * s * z⁻¹) := by group
    have heq : u * d * u⁻¹ * d⁻¹ = u * s * u⁻¹ * s⁻¹ := by
      rw [hd]
      calc u * (s * (z * s * z⁻¹)) * u⁻¹ * (s * (z * s * z⁻¹))⁻¹
          = u * s * ((z * s * z⁻¹) * u⁻¹) * (s * (z * s * z⁻¹))⁻¹ := by group
        _ = u * s * (u⁻¹ * (z * s * z⁻¹)) * (s * (z * s * z⁻¹))⁻¹ := by rw [hXu]
        _ = u * s * u⁻¹ * s⁻¹ := by group
    rw [heq] at hcommN
    simpa [commutatorElement_def] using hcommN
  have hS₂_le_N : S₂ ≤ N := by
    rw [hs.conj_eq]
    rintro a ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using hNn.conj_mem x (hS₁_le_N hx) z
  have hlayer_le_N : layer K ≤ N := by
    rw [hs.layer_eq]; exact sup_le hS₁_le_N hS₂_le_N
  unfold normalClosureOf
  exact le_antisymm hN_le_layer hlayer_le_N

end CFSG.EvenSporadicStandard.HSStd.InvCent
