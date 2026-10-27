module

public import CFSG.LocalAnalysis.GH72.Sec4Basic
import CFSG.LocalAnalysis.GH72.Sec2
public import CFSG.LocalAnalysis.ZStar

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools

section ZStar

variable {G : Type} [Group G] [Finite G]

theorem IsIsolatedIn.conj_mul_inv_mem_O {H : Subgroup G} {t : G} (ht : IsIsolatedIn H t)
    {h : G} (hh : h ∈ H) : h * t * h⁻¹ * t⁻¹ ∈ O H := by
  obtain ⟨htH, ht2, hiso⟩ := ht
  letI : Fintype H := Fintype.ofFinite H
  let τ : H := ⟨t, htH⟩
  have hτ1 : τ ≠ 1 := fun h1 => by
    have h1' : t = 1 := congrArg Subtype.val h1
    rw [h1', orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hτ2 : τ * τ = 1 := Subtype.ext (by
    have h1 := pow_orderOf_eq_one t
    rw [ht2, pow_two] at h1
    exact h1)
  have hisolated : ∀ g : H, (g * τ * g⁻¹) * τ = τ * (g * τ * g⁻¹) → g * τ * g⁻¹ = τ := by
    intro g hg
    have hg' : Commute ((g : G) * t * (g : G)⁻¹) t := congrArg Subtype.val hg
    exact Subtype.ext (hiso g g.2 hg')
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar H τ hτ1 hτ2 hisolated
  exact ⟨_, le_oddCore_of_normal hNn hNodd (hN ⟨h, hh⟩), rfl⟩

theorem IsIsolatedIn.exists_mem_C {H : Subgroup G} {t : G} (ht : IsIsolatedIn H t) {h : G}
    (hh : h ∈ H) : ∃ c ∈ H ⊓ C t, c⁻¹ * h ∈ O H := by
  have htt : t * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rwa [ht.2.1, pow_two] at h1
  have hk : h⁻¹ * (t * h * t⁻¹) ∈ O H := by
    have h1 := ht.conj_mul_inv_mem_O (inv_mem hh)
    rw [inv_inv] at h1
    simpa only [mul_assoc] using h1
  obtain ⟨o, ho, hfix⟩ := exists_fixed_mem_coset (card_O_odd H) htt (le_normalizer_O H ht.1) hk
  refine ⟨h * o, mem_inf.2 ⟨mul_mem hh (map_subtype_le _ ho), ?_⟩, ?_⟩
  · rw [mem_centralizer_singleton_iff]
    calc h * o * t = t * (h * o) * t⁻¹ * t := by rw [hfix]
      _ = t * (h * o) := by group
  · have e : (h * o)⁻¹ * h = o⁻¹ := by group
    rw [e]
    exact inv_mem ho

end ZStar

end CFSG.GH72
