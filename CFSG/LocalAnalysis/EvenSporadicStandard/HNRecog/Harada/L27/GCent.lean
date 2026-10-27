module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.GCentA
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NRStab

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA CFSG.EvenSporadicStandard.HNRecog
  CFSG.RankThree.Literature.FSmith

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G} {n : G}

private lemma zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  have : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  exact this c

private lemma range_mul_comm {x y : G} (hx : x ∈ ι.range) (hy : y ∈ ι.range) :
    x * y = y * x := by
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
  obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hy
  rw [← map_mul, ← map_mul, mul_comm]

private lemma rhoX_rangeRestrict (h : Setting25 G t z z₁ ι zv R0 F) (g : ↥(Ngrp h)) :
    rhoX h ((rho0 h).rangeRestrict g) =
      ((rho0 h g : TauCeti.QuadraticMap.orthogonalGroup (qW h)) : Wsp h ≃ₗ[ZMod 2] Wsp h) :=
  rfl

private lemma commute_vbar_inv (h : Setting25 G t z z₁ ι zv R0 F)
    (hn : n ∈ normalizer (ι.range : Set G)) {g : ↥(Ngrp h)}
    (hg : (rho0 h).rangeRestrict g * vbar h hn = vbar h hn * (rho0 h).rangeRestrict g) :
    (rho0 h).rangeRestrict g⁻¹ * vbar h hn = vbar h hn * (rho0 h).rangeRestrict g⁻¹ := by
  have hthis := (show Commute ((rho0 h).rangeRestrict g) (vbar h hn) from hg).inv_left
  rw [map_inv]
  exact hthis

theorem mem_Cgrp_or_mul_conj_t_mem_Cgrp (h : Setting25 G t z z₁ ι zv R0 F)
    (hn : n ∈ normalizer (ι.range : Set G)) (hnz : n * z₁ * n⁻¹ = z) {a : G}
    (ha : a ∈ ι.range) : a ∈ Cgrp ι zv ∨ a * (n * t * n⁻¹) ∈ Cgrp ι zv := by
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp ha
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp (conj_t_mem_range h hn)
  let vv : V6 := Multiplicative.toAdd y
  have hvv : coordElt ι vv = n * t * n⁻¹ := by
    change ι y = n * t * n⁻¹
    exact hy
  have hbil_vv : bil vv zv = 1 := by
    rcases zmod2_eq_zero_or_one (bil vv zv) with h0 | h1
    · exact absurd (by rw [← hvv]; exact (coordElt_mem_Cgrp h.injective_ι).mpr h0)
        (conj_t_not_mem_Cgrp h hn hnz)
    · exact h1
  by_cases hα0 : bil (Multiplicative.toAdd x) zv = 0
  · left
    show coordElt ι (Multiplicative.toAdd x) ∈ Cgrp ι zv
    exact (coordElt_mem_Cgrp h.injective_ι).mpr hα0
  · right
    have hα1 : bil (Multiplicative.toAdd x) zv = 1 := by
      rcases zmod2_eq_zero_or_one (bil (Multiplicative.toAdd x) zv) with h0 | h1
      · exact absurd h0 hα0
      · exact h1
    rw [← hvv]
    change coordElt ι (Multiplicative.toAdd x) * coordElt ι vv ∈ Cgrp ι zv
    rw [← coordElt_add]
    exact (coordElt_mem_Cgrp h.injective_ι).mpr (by
      rw [bil_add_left, hα1, hbil_vv]
      exact CharTwo.add_self_eq_zero 1)

theorem normalizes_Cgrp_of_commute_vbar (h : Setting25 G t z z₁ ι zv R0 F)
    (hn : n ∈ normalizer (ι.range : Set G)) (hnz : n * z₁ * n⁻¹ = z) {g : ↥(Ngrp h)}
    (hg : (rho0 h).rangeRestrict g * vbar h hn = vbar h hn * (rho0 h).rangeRestrict g)
    {a : G} (ha : a ∈ Cgrp ι zv) : (g : G) * a * (g : G)⁻¹ ∈ Cgrp ι zv := by
  have hR : a ∈ Rgrp h := Cgrp_le_Rgrp h ha
  have hu : toW h a hR ∈ A0W h := (mem_A0W_iff h hR).mpr ha
  refine (mem_A0W_iff h (conj_mem_Rgrp h g.2 hR)).mp ?_
  rw [← rho0_toW h g hR]
  have hcomm : rhoX h ((rho0 h).rangeRestrict g) * rhoX h (vbar h hn) =
      rhoX h (vbar h hn) * rhoX h ((rho0 h).rangeRestrict g) := by
    rw [← map_mul, ← map_mul, hg]
  rw [← ker_vbar_eq_A0W h hn hnz, LinearMap.mem_ker]
  rw [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  rw [← rhoX_rangeRestrict h g]
  change (rhoX h (vbar h hn) : Wsp h ≃ₗ[ZMod 2] Wsp h)
      ((rhoX h ((rho0 h).rangeRestrict g)) (toW h a hR)) =
    (rhoX h ((rho0 h).rangeRestrict g)) (toW h a hR)
  have h1 := congrArg (fun e : Wsp h ≃ₗ[ZMod 2] Wsp h => e (toW h a hR)) hcomm
  simp only [LinearEquiv.mul_apply] at h1
  rw [A0W_fixed_by_vbar h hn hu] at h1
  exact h1.symm

theorem conj_conj_t_mem_range_of_commute_vbar (h : Setting25 G t z z₁ ι zv R0 F)
    (hn : n ∈ normalizer (ι.range : Set G)) (hnz : n * z₁ * n⁻¹ = z) {g : ↥(Ngrp h)}
    (hg : (rho0 h).rangeRestrict g * vbar h hn = vbar h hn * (rho0 h).rangeRestrict g) :
    (g : G) * (n * t * n⁻¹) * (g : G)⁻¹ ∈ ι.range := by
  have hv_range : n * t * n⁻¹ ∈ ι.range := conj_t_mem_range h hn
  have hv_N : n * t * n⁻¹ ∈ Ngrp h := conj_t_mem_Ngrp h hn
  let gv : ↥(Ngrp h) := ⟨n * t * n⁻¹, hv_N⟩
  have hw_N : (g : G) * (n * t * n⁻¹) * (g : G)⁻¹ ∈ Ngrp h :=
    mul_mem (mul_mem g.2 hv_N) (inv_mem g.2)
  let gw : ↥(Ngrp h) := ⟨(g : G) * (n * t * n⁻¹) * (g : G)⁻¹, hw_N⟩
  have hcomm : rho0 h g * rho0 h gv = rho0 h gv * rho0 h g := by
    have h1 := congrArg (Subgroup.subtype (Xgrp h)) hg
    simp only [map_mul] at h1
    exact h1
  have hrho : rho0 h gw = rho0 h gv := by
    have hgw_eq : gw = g * gv * g⁻¹ := Subtype.ext rfl
    calc rho0 h gw = rho0 h (g * gv * g⁻¹) := by rw [hgw_eq]
      _ = rho0 h g * rho0 h gv * (rho0 h g)⁻¹ := by simp only [map_mul, map_inv]
      _ = rho0 h gv := by rw [hcomm]; group
  have hr_N : (n * t * n⁻¹)⁻¹ * ((g : G) * (n * t * n⁻¹) * (g : G)⁻¹) ∈ Ngrp h :=
    mul_mem (inv_mem hv_N) hw_N
  let r : G := (n * t * n⁻¹)⁻¹ * ((g : G) * (n * t * n⁻¹) * (g : G)⁻¹)
  have hrho_r : rho0 h ⟨r, hr_N⟩ = 1 := by
    have heq : (⟨r, hr_N⟩ : ↥(Ngrp h)) = gv⁻¹ * gw := Subtype.ext rfl
    rw [heq, map_mul, map_inv, hrho]
    simp
  have hr_R : r ∈ Rgrp h := (rho0_eq_one_iff h ⟨r, hr_N⟩).mp hrho_r
  have hc : ∀ a ∈ Cgrp ι zv, r * a = a * r := by
    intro a ha
    have ha_range : a ∈ ι.range := Cgrp_le_range ha
    have hva : (n * t * n⁻¹) * a = a * (n * t * n⁻¹) := range_mul_comm hv_range ha_range
    have hga : (g : G)⁻¹ * a * (g : G) ∈ Cgrp ι zv := by
      have hginv := commute_vbar_inv h hn hg
      have := normalizes_Cgrp_of_commute_vbar h hn hnz (g := g⁻¹) hginv ha
      simpa using this
    have hva' : (n * t * n⁻¹) * ((g : G)⁻¹ * a * (g : G)) =
        ((g : G)⁻¹ * a * (g : G)) * (n * t * n⁻¹) :=
      range_mul_comm hv_range (Cgrp_le_range hga)
    have hwa : ((g : G) * (n * t * n⁻¹) * (g : G)⁻¹) * a =
        a * ((g : G) * (n * t * n⁻¹) * (g : G)⁻¹) := by
      calc ((g : G) * (n * t * n⁻¹) * (g : G)⁻¹) * a
          = (g : G) * ((n * t * n⁻¹) * ((g : G)⁻¹ * a * (g : G))) * (g : G)⁻¹ := by
            group
        _ = (g : G) * (((g : G)⁻¹ * a * (g : G)) * (n * t * n⁻¹)) * (g : G)⁻¹ := by
            rw [hva']
        _ = a * ((g : G) * (n * t * n⁻¹) * (g : G)⁻¹) := by group
    have hva_inv : (n * t * n⁻¹)⁻¹ * a = a * (n * t * n⁻¹)⁻¹ :=
      (show Commute (n * t * n⁻¹) a from hva).inv_left
    show r * a = a * r
    rw [show r = (n * t * n⁻¹)⁻¹ * ((g : G) * (n * t * n⁻¹) * (g : G)⁻¹) from rfl]
    calc ((n * t * n⁻¹)⁻¹ * ((g : G) * (n * t * n⁻¹) * (g : G)⁻¹)) * a
        = (n * t * n⁻¹)⁻¹ * (((g : G) * (n * t * n⁻¹) * (g : G)⁻¹) * a) := by group
      _ = (n * t * n⁻¹)⁻¹ * (a * ((g : G) * (n * t * n⁻¹) * (g : G)⁻¹)) := by rw [hwa]
      _ = ((n * t * n⁻¹)⁻¹ * a) * ((g : G) * (n * t * n⁻¹) * (g : G)⁻¹) := by group
      _ = (a * (n * t * n⁻¹)⁻¹) * ((g : G) * (n * t * n⁻¹) * (g : G)⁻¹) := by
            rw [hva_inv]
      _ = a * ((n * t * n⁻¹)⁻¹ * ((g : G) * (n * t * n⁻¹) * (g : G)⁻¹)) := by group
  have hr_C : r ∈ Cgrp ι zv := centralizer_A0_inf_Rgrp h hr_R hc
  have hw_eq : (g : G) * (n * t * n⁻¹) * (g : G)⁻¹ = (n * t * n⁻¹) * r := by
    rw [show r = (n * t * n⁻¹)⁻¹ * ((g : G) * (n * t * n⁻¹) * (g : G)⁻¹) from rfl]
    group
  rw [hw_eq]
  exact mul_mem hv_range (Cgrp_le_range hr_C)

private lemma conj_mem_range_of_mem_range (h : Setting25 G t z z₁ ι zv R0 F)
    (hn : n ∈ normalizer (ι.range : Set G)) (hnz : n * z₁ * n⁻¹ = z) {g : ↥(Ngrp h)}
    (hg : (rho0 h).rangeRestrict g * vbar h hn = vbar h hn * (rho0 h).rangeRestrict g)
    {a : G} (ha : a ∈ ι.range) : (g : G) * a * (g : G)⁻¹ ∈ ι.range := by
  rcases mem_Cgrp_or_mul_conj_t_mem_Cgrp h hn hnz ha with hC | hCv
  · exact Cgrp_le_range (normalizes_Cgrp_of_commute_vbar h hn hnz hg hC)
  · have h1 : (g : G) * (a * (n * t * n⁻¹)) * (g : G)⁻¹ ∈ Cgrp ι zv :=
      normalizes_Cgrp_of_commute_vbar h hn hnz hg hCv
    have h2 : (g : G) * (n * t * n⁻¹) * (g : G)⁻¹ ∈ ι.range :=
      conj_conj_t_mem_range_of_commute_vbar h hn hnz hg
    have heq : (g : G) * a * (g : G)⁻¹ =
        ((g : G) * (a * (n * t * n⁻¹)) * (g : G)⁻¹) *
          ((g : G) * (n * t * n⁻¹) * (g : G)⁻¹)⁻¹ := by group
    rw [heq]
    exact mul_mem (Cgrp_le_range h1) (inv_mem h2)

theorem mem_Kgrp_of_commute_vbar (h : Setting25 G t z z₁ ι zv R0 F)
    (hn : n ∈ normalizer (ι.range : Set G)) (hnz : n * z₁ * n⁻¹ = z) {g : ↥(Ngrp h)}
    (hg : (rho0 h).rangeRestrict g * vbar h hn = vbar h hn * (rho0 h).rangeRestrict g) :
    (g : G) ∈ Kgrp ι z := by
  change (g : G) ∈ normalizer (ι.range : Set G) ⊓ centralizer ({z} : Set G)
  rw [Subgroup.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [Subgroup.mem_set_normalizer_iff]
    intro a
    constructor
    · exact conj_mem_range_of_mem_range h hn hnz hg
    · intro ha
      have hginv := commute_vbar_inv h hn hg
      have hb : (g : G)⁻¹ * ((g : G) * a * (g : G)⁻¹) * (g : G) ∈ ι.range := by
        simpa using conj_mem_range_of_mem_range h hn hnz (g := g⁻¹) hginv ha
      have heq : (g : G)⁻¹ * ((g : G) * a * (g : G)⁻¹) * (g : G) = a := by group
      rwa [heq] at hb
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp (conj_z_of_mem_normalizer_Rgrp h g.2)

theorem centralizer_vbar_le (h : Setting25 G t z z₁ ι zv R0 F)
    (hn : n ∈ normalizer (ι.range : Set G)) (hnz : n * z₁ * n⁻¹ = z) :
    ∀ g : ↥(Xgrp h), g * vbar h hn = vbar h hn * g → g ∈ Fbar h n ⊔ zpowers (vbar h hn) := by
  intro g hg
  obtain ⟨g', hg'⟩ := MonoidHom.rangeRestrict_surjective (rho0 h) g
  have hg'' : (rho0 h).rangeRestrict g' * vbar h hn = vbar h hn * (rho0 h).rangeRestrict g' := by
    rw [hg']; exact hg
  have hgK : (g' : G) ∈ Kgrp ι z := mem_Kgrp_of_commute_vbar h hn hnz hg''
  have hmem := Kbar_le_sup h hn hnz hgK
  rwa [hg'] at hmem

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
