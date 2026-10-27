module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.GA0
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.GFpfA
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.GLagr

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA CFSG.EvenSporadicStandard.HNRecog
  CFSG.RankThree.Literature.FSmith

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G} {n : G}

theorem fixed_on_A0W (h : Setting25 G t z z₁ ι zv R0 F) (hn : n ∈ normalizer (ι.range : Set G))
    (hnz : n * z₁ * n⁻¹ = z) {f : G} (hf : f ∈ Fconj n F) (hf5 : orderOf f = 5) {u : Wsp h}
    (hu : u ∈ A0W h)
    (hfu : ((rho0 h ⟨f, Fconj_le_Ngrp h hn hnz hf⟩ : TauCeti.QuadraticMap.orthogonalGroup (qW h)) :
      Wsp h ≃ₗ[ZMod 2] Wsp h) u = u) : u = 0 := by
  obtain ⟨x, hxR, hxC, hu_eq⟩ := hu
  rw [← hu_eq] at hfu ⊢
  have h1 := rho0_toW h ⟨f, Fconj_le_Ngrp h hn hnz hf⟩ hxR
  have h2 : (f * x * f⁻¹) * x⁻¹ ∈ zpowers z :=
    (toW_eq_toW_iff h (conj_mem_Rgrp h (Fconj_le_Ngrp h hn hnz hf) hxR) hxR).1
      (h1.symm.trans hfu)
  exact (toW_eq_zero_iff h hxR).2 (mem_zpowers_of_order_five h hn hnz hf hf5 hxC h2)

theorem Fbar_fpf (h : Setting25 G t z z₁ ι zv R0 F) (hn : n ∈ normalizer (ι.range : Set G))
    (hnz : n * z₁ * n⁻¹ = z) :
    ∀ f ∈ Fbar h n, orderOf f = 5 →
      ∀ x : Wsp h, (rhoX h f : Wsp h ≃ₗ[ZMod 2] Wsp h) x = x → x = 0 := by
  intro fbar hfbar hf5 x hx
  obtain ⟨f, hf, hfbar_eq⟩ := (mem_Fbar_iff h hn hnz).1 hfbar
  let φ : ↥(Fconj n F) →* ↥(Xgrp h) :=
    (rho0 h).rangeRestrict.comp (Subgroup.inclusion (Fconj_le_Ngrp h hn hnz))
  have hφf : φ ⟨f, hf⟩ = fbar := by
    simp only [φ, MonoidHom.comp_apply]
    rw [show Subgroup.inclusion (Fconj_le_Ngrp h hn hnz) ⟨f, hf⟩ =
        ⟨f, Fconj_le_Ngrp h hn hnz hf⟩ from rfl]
    exact hfbar_eq
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h1 : φ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((φ (a * b⁻¹) : ↥(Xgrp h)) :
        TauCeti.QuadraticMap.orthogonalGroup (qW h)) = 1 :=
      congrArg (fun z : ↥(Xgrp h) =>
        (z : TauCeti.QuadraticMap.orthogonalGroup (qW h))) h1
    have hsub : (⟨((a * b⁻¹ : ↥(Fconj n F)) : G),
        Fconj_le_Ngrp h hn hnz (a * b⁻¹).2⟩ : ↥(Ngrp h)) =
        Subgroup.inclusion (Fconj_le_Ngrp h hn hnz) (a * b⁻¹) := rfl
    have h3 : rho0 h ⟨((a * b⁻¹ : ↥(Fconj n F)) : G),
        Fconj_le_Ngrp h hn hnz (a * b⁻¹).2⟩ = 1 := by
      rw [hsub]
      simpa [φ, MonoidHom.comp_apply, MonoidHom.coe_rangeRestrict] using h2
    have h4 : ((a * b⁻¹ : ↥(Fconj n F)) : G) = 1 :=
      rho0_injOn_Fconj h hn hnz (a * b⁻¹).2 h3
    exact mul_inv_eq_one.mp (Subtype.ext h4)
  have hord : orderOf f = 5 := by
    have h1 : orderOf (⟨f, hf⟩ : ↥(Fconj n F)) = 5 := by
      rw [← orderOf_injective φ hφinj ⟨f, hf⟩, hφf, hf5]
    rwa [Subgroup.orderOf_mk] at h1
  have hrhoX : (rhoX h fbar : Wsp h ≃ₗ[ZMod 2] Wsp h) =
      ((rho0 h ⟨f, Fconj_le_Ngrp h hn hnz hf⟩ :
        TauCeti.QuadraticMap.orthogonalGroup (qW h)) : Wsp h ≃ₗ[ZMod 2] Wsp h) := by
    rw [← hfbar_eq]
    rfl
  have hU : ∀ w : Wsp h, (∀ u ∈ A0W h, (qW h).polarBilin w u = 0) → w ∈ A0W h := by
    intro w hw
    exact A0W_orth_le h w (fun u hu => by
      have := hw u hu
      rwa [QuadraticMap.polarBilin_apply_apply] at this)
  have hfU : ∀ u ∈ A0W h, (rhoX h fbar : Wsp h ≃ₗ[ZMod 2] Wsp h) u ∈ A0W h := by
    intro u hu
    have hstab := A0W_stable h (k := f) (Fconj_le_K h hn hnz hf) hu
    rw [hrhoX]
    exact hstab
  have hfix : ∀ u ∈ A0W h, (rhoX h fbar : Wsp h ≃ₗ[ZMod 2] Wsp h) u = u → u = 0 := by
    intro u hu huu
    refine fixed_on_A0W h hn hnz hf hord hu ?_
    rwa [← hrhoX]
  exact fpf_of_fpf_on_lagrangian (W := Wsp h) (B := (qW h).polarBilin) (U := A0W h)
    hU (rhoX h fbar) (rhoX_polar h fbar) hfU hfix x hx

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
