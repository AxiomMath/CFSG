module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.M22Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.OneClass

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.M23Std (OneClassData)

theorem m22_oneClassData
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : StdHyp G L) (hL : IsSporadic L .M22)
    {z t : G} (hz : z ∈ centralizer (L : Set G)) (hz2 : orderOf z = 2)
    (hC : centralizer ({z} : Set G) ≤ L ⊔ zpowers z) (ht : t ∈ L) (ht2 : orderOf t = 2) :
    OneClassData L z t := by
  have := h.simple
  have hZ : center L = ⊥ := center_eq_bot_of_isSporadic hL
  have hS := card_sylow_eq_two_of_isSporadic h hL
  have hinn : centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G) :=
    hC.trans (sup_le_sup_left (zpowers_le.2 hz) L)
  obtain ⟨hC', hd, hcomm⟩ := h.centralizer_eq_prod_of_center_eq_bot hS hz hz2 hinn hZ
  obtain ⟨e⟩ := hL
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hz2; exact absurd hz2 (by decide)
  have ht1 : t ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ht2; exact absurd ht2 (by decide)
  have hzpow : ∀ b ∈ Subgroup.zpowers z, b = 1 ∨ b = z := by
    intro b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    rw [← zpow_mod_orderOf, hz2]
    rcases Int.emod_two_eq_zero_or_one k with h0 | h0
    · left; simp [h0]
    · right; simp [h0]
  have hord : ∀ u : L, u * u = 1 → u ≠ 1 → orderOf (e u) = 2 := by
    intro u hu2 hu1
    rw [MulEquiv.orderOf_eq e]
    exact orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
  let t' : L := ⟨t, ht⟩
  have ht'2 : t' * t' = 1 := Subtype.ext (by simpa using htt)
  have ht'1 : t' ≠ 1 := fun h1 => ht1 (congrArg Subtype.val h1)
  exact
    { z_mul_self := hzz
      z_ne_one := hz1
      t_mul_self := htt
      t_ne_one := ht1
      t_mem := ht
      z_comm := fun l hl => (mem_centralizer_iff.1 hz l hl).symm
      z_not_mem := fun hzL => hz1 (mem_bot.1 (hd.le_bot ⟨hzL, mem_zpowers z⟩))
      centralizer_z := by
        intro g hg
        have hg' : g ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 hg.symm
        rw [hC'] at hg'
        obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hcomm hg'
        rcases hzpow b hb with rfl | rfl
        · exact ⟨a, ha, Or.inl (by simp)⟩
        · exact ⟨a, ha, Or.inr rfl⟩
      oneClass := by
        intro u hu hu2 hu1
        let u' : L := ⟨u, hu⟩
        have hu'2 : u' * u' = 1 := Subtype.ext (by simpa using hu2)
        have hu'1 : u' ≠ 1 := fun h1 => hu1 (congrArg Subtype.val h1)
        obtain ⟨c₁, hc₁⟩ := m22_involution_conj (e u') (hord u' hu'2 hu'1)
        obtain ⟨c₂, hc₂⟩ := m22_involution_conj (e t') (hord t' ht'2 ht'1)
        refine ⟨((e.symm (c₁ * c₂⁻¹) : L) : G), (e.symm (c₁ * c₂⁻¹) : L).2, ?_⟩
        have hx : u' = e.symm (c₁ * c₂⁻¹) * t' * (e.symm (c₁ * c₂⁻¹))⁻¹ := by
          apply e.injective
          rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hc₁, hc₂]
          group
        simpa using congrArg Subtype.val hx
      t_sq := by
        obtain ⟨s, hs⟩ := m22_involution_isSq (hord t' ht'2 ht'1)
        refine ⟨((e.symm s : L) : G), (e.symm s : L).2, ?_⟩
        have : e.symm s * e.symm s = t' := by
          apply e.injective
          rw [map_mul, MulEquiv.apply_symm_apply, hs]
        simpa using congrArg Subtype.val this }

end CFSG.EvenSporadicStandard.M22Std
