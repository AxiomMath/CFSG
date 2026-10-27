module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwConjG
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwAgrp
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.WpGTypes
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwDefs

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {ι : Perm (Fin 10) →* G}

private theorem tw_liftS8_abType22_val :
    liftS8 (abType22 : Perm (Fin 8)) = (swap 0 1 * swap 2 3 : Perm (Fin 10)) := by
  change liftS8 (swap 0 1 * swap 2 3 : Perm (Fin 8)) =
    (swap 0 1 * swap 2 3 : Perm (Fin 10))
  rw [map_mul, liftS8_swap, liftS8_swap]
  decide

theorem exists_conj_abar (hC : CentData z ι) (hx : IsConj z (ι τ₀))
    (hP2 : ¬ IsConj z (z * ι τ₀)) (hp : pairOrder (ι τ₀) (ι (swap 0 1)) = N10 2)
    {Sg : Subgroup (TwoSec (z * ι τ₀))}
    (hAbar : ((Agrp ι).subgroupOf (centralizer ({z * ι τ₀} : Set G))).map
        (QuotientGroup.mk' (zpowers (selfC (z * ι τ₀)))) =
      (⁅Sg, Sg⁆ : Subgroup (TwoSec (z * ι τ₀)))) :
    ∃ (y a : TwoSec (z * ι τ₀)) (ha : a ∈ (⁅Sg, Sg⁆ : Subgroup (TwoSec (z * ι τ₀))))
      (eA : (⁅Sg, Sg⁆ : Subgroup (TwoSec (z * ι τ₀))) ≃* alternatingGroup (Fin 8)),
      y * y = 1 ∧
        y * (QuotientGroup.mk ⟨z, z_mem_centralizer_x₂ hC⟩ : TwoSec (z * ι τ₀)) * y⁻¹ =
          (QuotientGroup.mk ⟨z, z_mem_centralizer_x₂ hC⟩ : TwoSec (z * ι τ₀)) * a ∧
        eA ⟨a, ha⟩ = abType22 := by
  obtain ⟨s, hs, hss, hsz⟩ := exists_conj_z_mul_a hC hx hP2 hp
  let C : Subgroup G := centralizer ({z * ι τ₀} : Set G)
  let g : alternatingGroup (Fin 8) →* G :=
    (ι.comp liftS8).comp (alternatingGroup (Fin 8)).subtype
  have hmem : ∀ ρ : alternatingGroup (Fin 8), g ρ ∈ C := by
    intro ρ
    exact Agrp_le_centralizer_x₂ hC (mem_Agrp_iff.2 ⟨(ρ : Perm (Fin 8)), ρ.2, rfl⟩)
  let N : Subgroup ↥C := zpowers (selfC (z * ι τ₀))
  haveI : N.Normal := normal_zpowers_selfC (z * ι τ₀)
  let f : alternatingGroup (Fin 8) →* TwoSec (z * ι τ₀) :=
    (QuotientGroup.mk' N).comp (g.codRestrict C hmem)
  have hker : ∀ ρ : alternatingGroup (Fin 8), f ρ = 1 → ρ = 1 := by
    intro ρ hρ
    have hmemq : (g.codRestrict C hmem) ρ ∈ N :=
      (QuotientGroup.eq_one_iff ((g.codRestrict C hmem) ρ)).1 hρ
    rcases (mem_zpowers_selfC_iff (x₂_mul_self hC)).1 hmemq with h1 | h2
    · have h1' : ι (liftS8 (ρ : Perm (Fin 8))) = 1 := h1
      apply Subtype.ext
      change (ρ : Perm (Fin 8)) = 1
      apply liftS8_injective
      rw [map_one]
      exact hC.inj (h1'.trans (map_one ι).symm)
    · exfalso
      have h2' : ι (liftS8 (ρ : Perm (Fin 8))) = z * ι τ₀ := h2
      have hz : z = ι (liftS8 (ρ : Perm (Fin 8)) * τ₀⁻¹) := by
        calc z = (z * ι τ₀) * (ι τ₀)⁻¹ := by group
          _ = ι (liftS8 (ρ : Perm (Fin 8))) * (ι τ₀)⁻¹ := by rw [← h2']
          _ = ι (liftS8 (ρ : Perm (Fin 8))) * ι τ₀⁻¹ := by rw [← map_inv]
          _ = ι (liftS8 (ρ : Perm (Fin 8)) * τ₀⁻¹) := by rw [← map_mul]
      exact hC.ne_z _ hz.symm
  have hf : Function.Injective f := by
    intro ρ σ h
    have h1 : ρ * σ⁻¹ = 1 :=
      hker (ρ * σ⁻¹) (by rw [map_mul, map_inv, h, mul_inv_cancel])
    exact mul_inv_eq_one.mp h1
  let A' : Subgroup ↥C := (Agrp ι).subgroupOf C
  have hrangeA : f.range = A'.map (QuotientGroup.mk' N) := by
    apply le_antisymm
    · rintro y hy
      obtain ⟨ρ, rfl⟩ := MonoidHom.mem_range.1 hy
      refine Subgroup.mem_map.2 ⟨(g.codRestrict C hmem) ρ, ?_, rfl⟩
      exact mem_Agrp_iff.2 ⟨(ρ : Perm (Fin 8)), ρ.2, rfl⟩
    · rintro y ⟨c, hc, rfl⟩
      rw [MonoidHom.mem_range]
      obtain ⟨ρ, hρ, hρeq⟩ := mem_Agrp_iff.1 (show (c : G) ∈ Agrp ι from hc)
      refine ⟨⟨ρ, hρ⟩, ?_⟩
      have hc_eq : c = (g.codRestrict C hmem) ⟨ρ, hρ⟩ := by
        apply Subtype.ext
        exact hρeq.symm
      rw [hc_eq]
      rfl
  have hrange : f.range = (⁅Sg, Sg⁆ : Subgroup (TwoSec (z * ι τ₀))) :=
    hrangeA.trans hAbar
  let eA : (⁅Sg, Sg⁆ : Subgroup (TwoSec (z * ι τ₀))) ≃* alternatingGroup (Fin 8) :=
    (MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hf).symm
  have heA_apply : ∀ (ρ : alternatingGroup (Fin 8))
      (h : f ρ ∈ (⁅Sg, Sg⁆ : Subgroup (TwoSec (z * ι τ₀)))), eA ⟨f ρ, h⟩ = ρ := by
    intro ρ h
    dsimp only [eA]
    rw [MulEquiv.trans_apply]
    apply (MonoidHom.ofInjective hf).injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]
  let hz : z ∈ C := z_mem_centralizer_x₂ hC
  let y : TwoSec (z * ι τ₀) := QuotientGroup.mk' N ⟨s, hs⟩
  have hyy : y * y = 1 := by
    have hs2 : (⟨s, hs⟩ * ⟨s, hs⟩ : ↥C) = 1 := by
      apply Subtype.ext
      exact hss
    dsimp only [y]
    rw [← map_mul, hs2, map_one]
  have hc0 : (⟨s, hs⟩ * ⟨z, hz⟩ * ⟨s, hs⟩⁻¹ : ↥C) =
      ⟨z, hz⟩ * (g.codRestrict C hmem) abType22 := by
    apply Subtype.ext
    show s * z * s⁻¹ = z * ι (liftS8 (abType22 : Perm (Fin 8)))
    rw [hsz, tw_liftS8_abType22_val]
  have hy : y * (QuotientGroup.mk' N ⟨z, hz⟩) * y⁻¹ =
      (QuotientGroup.mk' N ⟨z, hz⟩) * f abType22 := by
    change QuotientGroup.mk' N (⟨s, hs⟩ * ⟨z, hz⟩ * ⟨s, hs⟩⁻¹) =
      QuotientGroup.mk' N (⟨z, hz⟩ * (g.codRestrict C hmem) abType22)
    rw [hc0]
  have ha : f abType22 ∈ (⁅Sg, Sg⁆ : Subgroup (TwoSec (z * ι τ₀))) := by
    rw [← hrange]
    exact MonoidHom.mem_range.2 ⟨abType22, rfl⟩
  refine ⟨y, f abType22, ha, eA, hyy, hy, ?_⟩
  exact heA_apply abType22 ha

end CFSG.OddStandard.AltStdSec.SwapPartner
