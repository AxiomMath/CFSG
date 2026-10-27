module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NMAExtra

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G}

theorem Setting25.t_mem_Rgrp (h : Setting25 G t z z₁ ι zv R0 F) : t ∈ Rgrp h := by
  have ht : t ∈ Cgrp ι zv := by
    rw [← h.ι_tv]
    exact (coordElt_mem_Cgrp h.injective_ι).2 h.bil_tv_zv
  exact Cgrp_le_Rgrp h ht

theorem centralizer_Rgrp_eq (h : Setting25 G t z z₁ ι zv R0 F) :
    centralizer (Rgrp h : Set G) = zpowers z := by
  refine le_antisymm ?_ ?_
  · intro c hc
    have hcR : ∀ y ∈ Rgrp h, c * y = y * c :=
      fun y hy => (Subgroup.mem_centralizer_iff.mp hc y hy).symm
    have hct : c * t = t * c := hcR t (Setting25.t_mem_Rgrp h)
    have hcz : c * z = z * c := hcR z (z_mem_Rgrp h)
    have hcC : c ∈ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) := by
      rw [Subgroup.mem_inf]
      exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr hct,
        Subgroup.mem_centralizer_singleton_iff.mpr hcz⟩
    have hfaith : ∀ x ∈ R0, c * x * c⁻¹ * x⁻¹ ∈ zpowers z := by
      intro x hx
      have hcx : c * x = x * c := hcR x (R0_le_Rgrp h hx)
      have h1 : c * x * c⁻¹ * x⁻¹ = 1 := by rw [hcx]; group
      rw [h1]
      exact one_mem _
    have hcR0 : c ∈ R0 := h.hD2.R0_faith c hcC hfaith
    have hcR' : c ∈ Rgrp h := R0_le_Rgrp h hcR0
    exact Rgrp_center_le h hcR' hcR
  · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (Subgroup.mem_inf.mp (Rgrp_le_K h hy)).2

end CFSG.EvenSporadicStandard.HNRecog.Harada
