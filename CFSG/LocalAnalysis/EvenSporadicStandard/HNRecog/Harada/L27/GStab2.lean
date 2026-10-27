module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.GStab
public import CFSG.GF2Type.Smith1979.W4C1Orth

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA CFSG.EvenSporadicStandard.HNRecog
  CFSG.RankThree.Literature.FSmith

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G}

private lemma rangeRestrict_eq_one_iff {M N : Type*} [Group M] [Group N] (f : M →* N) (x : M) :
    f.rangeRestrict x = 1 ↔ f x = 1 := by
  rw [Subtype.ext_iff]
  simp [MonoidHom.coe_rangeRestrict]

private lemma mem_R0_iff_mem_Rgrp (h : Setting25 G t z z₁ ι zv R0 F) (hzt : ¬ IsConj t z)
    (htz : IsConj t (t * z)) {c : G}
    (hc : c ∈ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G)) :
    c ∈ R0 ↔ c ∈ Rgrp h := by
  have hRt : Rgrp h ⊓ centralizer ({t} : Set G) = R0 := Rgrp_inf_centralizer_t h hzt htz
  have hct : c ∈ centralizer ({t} : Set G) := (Subgroup.mem_inf.mp hc).1
  constructor
  · intro hcR0
    have hmem : c ∈ Rgrp h ⊓ centralizer ({t} : Set G) := by rw [hRt]; exact hcR0
    exact (Subgroup.mem_inf.mp hmem).1
  · intro hcR
    have hmem : c ∈ Rgrp h ⊓ centralizer ({t} : Set G) := ⟨hcR, hct⟩
    rwa [hRt] at hmem

theorem mem_Pgrp_of_stab (h : Setting25 G t z z₁ ι zv R0 F) (hzt : ¬ IsConj t z)
    (htz : IsConj t (t * z)) {g : ↥(Xgrp h)}
    (hg : ((rhoX h g : Wsp h ≃ₗ[ZMod 2] Wsp h)) (wvec h) = wvec h) : g ∈ Pgrp h := by
  obtain ⟨g₀, hg₀⟩ := MonoidHom.rangeRestrict_surjective (rho0 h) g
  have hg₀fix : (rho0 h g₀ : Wsp h ≃ₗ[ZMod 2] Wsp h) (wvec h) = wvec h := by
    have h1 : rhoX h ((rho0 h).rangeRestrict g₀) =
        (rho0 h g₀ : Wsp h ≃ₗ[ZMod 2] Wsp h) := rfl
    rw [← hg₀, h1] at hg
    exact hg
  have htw : toW h ((g₀ : G) * t * (g₀ : G)⁻¹)
      (conj_mem_Rgrp h g₀.2 (Setting25.t_mem_Rgrp h)) = wvec h := by
    rw [← rho0_toW h g₀ (Setting25.t_mem_Rgrp h)]
    simpa only [wvec] using hg₀fix
  have hmem : ((g₀ : G) * t * (g₀ : G)⁻¹) * t⁻¹ ∈ zpowers z :=
    (toW_eq_toW_iff h (conj_mem_Rgrp h g₀.2 (Setting25.t_mem_Rgrp h))
      (Setting25.t_mem_Rgrp h)).1 (by simpa only [wvec] using htw)
  have hord : orderOf z = 2 := orderOf_eq_prime h.z_sq h.z_ne_one
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rw [← zpow_mod_orderOf z k, hord] at hk
  norm_num only [Nat.cast_ofNat] at hk
  rcases Int.emod_two_eq_zero_or_one k with hk2 | hk2
  ·
    rw [hk2] at hk
    have hgt : (g₀ : G) * t * (g₀ : G)⁻¹ = t := by
      have h1 : ((g₀ : G) * t * (g₀ : G)⁻¹) * t⁻¹ = 1 := by simpa using hk.symm
      exact mul_inv_eq_one.mp h1
    have hmemC : (g₀ : G) ∈ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) := by
      rw [Subgroup.mem_inf]
      refine ⟨?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact mul_inv_eq_iff_eq_mul.mp hgt
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact mul_inv_eq_iff_eq_mul.mp (conj_z_of_mem_normalizer_Rgrp h g₀.2)
    rw [← hg₀, Pgrp]
    exact Subgroup.mem_map.mpr ⟨g₀, Subgroup.mem_subgroupOf.mpr hmemC, rfl⟩
  ·
    rw [hk2] at hk
    have hgt : (g₀ : G) * t * (g₀ : G)⁻¹ = t * z := by
      have h1 : ((g₀ : G) * t * (g₀ : G)⁻¹) * t⁻¹ = z := by simpa using hk.symm
      rw [h.t_mul_z_comm]
      exact mul_inv_eq_iff_eq_mul.mp h1
    obtain ⟨r, hr, hr_conj⟩ := exists_conj_t_mul_z h hzt htz
    let rN : ↥(Ngrp h) := ⟨r, Rgrp_le_Ngrp h hr⟩
    let g₁ : ↥(Ngrp h) := rN⁻¹ * g₀
    have hg₁t : (g₁ : G) * t * (g₁ : G)⁻¹ = t := by
      have h1 : r⁻¹ * (t * z) * r = t := by
        have h2 : r⁻¹ * (r * t * r⁻¹) * r = t := by group
        rwa [hr_conj] at h2
      have hcoe : (g₁ : G) = r⁻¹ * (g₀ : G) := rfl
      calc (g₁ : G) * t * (g₁ : G)⁻¹
          = r⁻¹ * ((g₀ : G) * t * (g₀ : G)⁻¹) * r := by rw [hcoe]; group
        _ = r⁻¹ * (t * z) * r := by rw [hgt]
        _ = t := h1
    have hg₁z : (g₁ : G) * z * (g₁ : G)⁻¹ = z := by
      have hr_z : r⁻¹ * z * r = z := by
        have hcomm : r * z = z * r :=
          Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (Rgrp_le_K h hr)).2
        calc r⁻¹ * z * r = r⁻¹ * (z * r) := by rw [mul_assoc]
          _ = r⁻¹ * (r * z) := by rw [← hcomm]
          _ = (r⁻¹ * r) * z := by rw [mul_assoc]
          _ = z := by rw [inv_mul_cancel, one_mul]
      have hcoe : (g₁ : G) = r⁻¹ * (g₀ : G) := rfl
      calc (g₁ : G) * z * (g₁ : G)⁻¹
          = r⁻¹ * ((g₀ : G) * z * (g₀ : G)⁻¹) * r := by rw [hcoe]; group
        _ = r⁻¹ * z * r := by rw [conj_z_of_mem_normalizer_Rgrp h g₀.2]
        _ = z := hr_z
    have hmemC : (g₁ : G) ∈ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) := by
      rw [Subgroup.mem_inf]
      exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hg₁t),
        Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hg₁z)⟩
    have hρ : (rho0 h).rangeRestrict g₁ = g := by
      rw [← hg₀]
      apply Subtype.ext
      rw [MonoidHom.coe_rangeRestrict, MonoidHom.coe_rangeRestrict]
      have hr'0 : rho0 h rN = 1 := by
        rw [← MonoidHom.mem_ker, ker_rho0 h]
        exact Subgroup.mem_subgroupOf.mpr hr
      show rho0 h g₁ = rho0 h g₀
      rw [show g₁ = rN⁻¹ * g₀ from rfl, map_mul, map_inv, hr'0, inv_one, one_mul]
    rw [← hρ, Pgrp]
    exact Subgroup.mem_map.mpr ⟨g₁, Subgroup.mem_subgroupOf.mpr hmemC, rfl⟩

theorem Pgrp_iso (h : Setting25 G t z z₁ ι zv R0 F) (hzt : ¬ IsConj t z)
    (htz : IsConj t (t * z)) (hS5 : CzS5 t z R0) :
    Nonempty (↥(Pgrp h) ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨ψ, hψsurj, hψker⟩ := hS5
  let C : Subgroup G := centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G)
  let φ : ↥C →* ↥(Xgrp h) :=
    (rho0 h).rangeRestrict.comp (Subgroup.inclusion (Czgrp_le_Ngrp h hzt htz))
  have hφrange : φ.range = Pgrp h := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_range] at hx
      obtain ⟨c, rfl⟩ := hx
      rw [Pgrp, Subgroup.mem_map]
      exact ⟨Subgroup.inclusion (Czgrp_le_Ngrp h hzt htz) c,
        Subgroup.mem_subgroupOf.mpr c.2, rfl⟩
    · intro hx
      rw [Pgrp, Subgroup.mem_map] at hx
      obtain ⟨n, hn, rfl⟩ := hx
      rw [MonoidHom.mem_range]
      refine ⟨⟨(n : G), Subgroup.mem_subgroupOf.mp hn⟩, ?_⟩
      show (rho0 h).rangeRestrict (Subgroup.inclusion (Czgrp_le_Ngrp h hzt htz)
        ⟨(n : G), Subgroup.mem_subgroupOf.mp hn⟩) = (rho0 h).rangeRestrict n
      rw [show Subgroup.inclusion (Czgrp_le_Ngrp h hzt htz)
          ⟨(n : G), Subgroup.mem_subgroupOf.mp hn⟩ = n from Subtype.ext rfl]
  have hφker : φ.ker = R0.subgroupOf C := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have hφc : φ c = (rho0 h).rangeRestrict
        (Subgroup.inclusion (Czgrp_le_Ngrp h hzt htz) c) := rfl
    rw [hφc, rangeRestrict_eq_one_iff, ← MonoidHom.mem_ker, ker_rho0 h, Subgroup.mem_subgroupOf]
    rw [show ((Subgroup.inclusion (Czgrp_le_Ngrp h hzt htz) c : ↥(Ngrp h)) : G) = (c : G) from rfl]
    exact (mem_R0_iff_mem_Rgrp h hzt htz c.2).symm
  refine ⟨(MulEquiv.subgroupCongr hφrange).symm.trans
    ((QuotientGroup.quotientKerEquivRange φ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (hφker.trans hψker.symm)).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj)))⟩

theorem card_Xgrp_le (h : Setting25 G t z z₁ ι zv R0 F) (hzt : ¬ IsConj t z)
    (htz : IsConj t (t * z)) (hS5 : CzS5 t z R0) : Nat.card (Xgrp h) ≤ 16200 := by
  obtain ⟨e⟩ := Pgrp_iso h hzt htz hS5
  haveI : FiniteDimensional (ZMod 2) (Wsp h) := Module.Finite.of_finite
  have hbound := CFSG.GF2Type.Smith1979.W4C1.card_le_mul_stabSub (rhoX h)
    (nondegenerate_qW h) (finrank_Wsp h) (fun m => m.1.2) (wvec_ne_zero h hzt htz) (qW_wvec h)
  have hle : CFSG.GF2Type.Smith1979.W4C1.stabSub (rhoX h) (wvec h) ≤ Pgrp h := by
    intro m hm
    exact mem_Pgrp_of_stab h hzt htz
      (Iff.mp (CFSG.GF2Type.Smith1979.W4C1.mem_stabSub (rhoX h)) hm)
  have hcard2 : Nat.card (CFSG.GF2Type.Smith1979.W4C1.stabSub (rhoX h) (wvec h)) ≤
      Nat.card (Pgrp h) := Subgroup.card_le_of_le hle
  have hcardP : Nat.card (Pgrp h) = 120 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    norm_num
  calc Nat.card (Xgrp h)
      ≤ 135 * Nat.card (CFSG.GF2Type.Smith1979.W4C1.stabSub (rhoX h) (wvec h)) := hbound
    _ ≤ 135 * Nat.card (Pgrp h) := Nat.mul_le_mul_left 135 hcard2
    _ = 135 * 120 := by rw [hcardP]
    _ = 16200 := by norm_num

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
