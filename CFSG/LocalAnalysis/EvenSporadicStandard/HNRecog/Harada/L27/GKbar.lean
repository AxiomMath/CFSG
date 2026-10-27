module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.GBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NMAComp2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA CFSG.EvenSporadicStandard.HNRecog
  CFSG.RankThree.Literature.FSmith

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G} {n : G}

theorem Kgrp_le_Ngrp (h : Setting25 G t z z₁ ι zv R0 F) : Kgrp ι z ≤ Ngrp h := by
  intro k hk
  change k ∈ Subgroup.normalizer (Rgrp h : Set G)
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  constructor
  · exact fun hx => Rgrp_conj h hk hx
  · intro hy
    have h := Rgrp_conj h (inv_mem hk) hy
    have hx' : k⁻¹ * (k * x * k⁻¹) * (k⁻¹)⁻¹ = x := by group
    rwa [hx'] at h

theorem Fconj_le_Ngrp (h : Setting25 G t z z₁ ι zv R0 F) (hn : n ∈ normalizer (ι.range : Set G))
    (hnz : n * z₁ * n⁻¹ = z) : Fconj n F ≤ Ngrp h :=
  (Fconj_le_K h hn hnz).trans (Kgrp_le_Ngrp h)

theorem conj_t_mem_Ngrp (h : Setting25 G t z z₁ ι zv R0 F)
    (hn : n ∈ normalizer (ι.range : Set G)) : n * t * n⁻¹ ∈ Ngrp h :=
  Kgrp_le_Ngrp h (Setting25.range_le_K h (conj_t_mem_range h hn))

theorem Qgrp_le_Ngrp (h : Setting25 G t z z₁ ι zv R0 F) (hn : n ∈ normalizer (ι.range : Set G))
    (hnz : n * z₁ * n⁻¹ = z) : Qgrp h n ≤ Ngrp h :=
  (Qgrp_le_K h hn hnz).trans (Kgrp_le_Ngrp h)

@[expose] noncomputable def Fbar (h : Setting25 G t z z₁ ι zv R0 F) (n : G) :
    Subgroup ↥(Xgrp h) :=
  ((Fconj n F).subgroupOf (Ngrp h)).map (rho0 h).rangeRestrict

@[expose] noncomputable def vbar (h : Setting25 G t z z₁ ι zv R0 F)
    (hn : n ∈ normalizer (ι.range : Set G)) : ↥(Xgrp h) :=
  (rho0 h).rangeRestrict ⟨n * t * n⁻¹, conj_t_mem_Ngrp h hn⟩

theorem rho0_eq_one_iff (h : Setting25 G t z z₁ ι zv R0 F) (g : ↥(Ngrp h)) :
    rho0 h g = 1 ↔ (g : G) ∈ Rgrp h := by
  rw [← MonoidHom.mem_ker, ker_rho0 h]
  rfl

private theorem rangeRestrict_eq_one_of_mem_Rgrp (h : Setting25 G t z z₁ ι zv R0 F) {x : G}
    (hx : x ∈ Rgrp h) :
    (rho0 h).rangeRestrict ⟨x, Rgrp_le_Ngrp h hx⟩ = 1 := by
  apply Subtype.ext
  simpa using (rho0_eq_one_iff h ⟨x, Rgrp_le_Ngrp h hx⟩).mpr hx

theorem mem_Fbar_iff (h : Setting25 G t z z₁ ι zv R0 F) (hn : n ∈ normalizer (ι.range : Set G))
    (hnz : n * z₁ * n⁻¹ = z) {x : ↥(Xgrp h)} :
    x ∈ Fbar h n ↔ ∃ (f : G) (hf : f ∈ Fconj n F),
      (rho0 h).rangeRestrict ⟨f, Fconj_le_Ngrp h hn hnz hf⟩ = x := by
  constructor
  · intro hx
    rw [Fbar, Subgroup.mem_map] at hx
    obtain ⟨a, ha, hax⟩ := hx
    refine ⟨(a : G), Subgroup.mem_subgroupOf.mp ha, ?_⟩
    have hEq : (⟨(a : G), Fconj_le_Ngrp h hn hnz (Subgroup.mem_subgroupOf.mp ha)⟩ :
        ↥(Ngrp h)) = a := Subtype.ext rfl
    rw [hEq]
    exact hax
  · rintro ⟨f, hf, hfx⟩
    rw [Fbar, Subgroup.mem_map]
    exact ⟨⟨f, Fconj_le_Ngrp h hn hnz hf⟩, Subgroup.mem_subgroupOf.mpr hf, hfx⟩

theorem rho0_injOn_Fconj (h : Setting25 G t z z₁ ι zv R0 F)
    (hn : n ∈ normalizer (ι.range : Set G)) (hnz : n * z₁ * n⁻¹ = z) {f : G}
    (hf : f ∈ Fconj n F) (h1 : rho0 h ⟨f, Fconj_le_Ngrp h hn hnz hf⟩ = 1) : f = 1 := by
  have hfR : f ∈ Rgrp h := (rho0_eq_one_iff h ⟨f, Fconj_le_Ngrp h hn hnz hf⟩).mp h1
  have hfQ : f ∈ Qgrp h n := (mem_Qgrp h).mpr ⟨1, one_mem _, f, hf, (one_mul f).symm⟩
  exact Subgroup.mem_bot.mp
    ((disjoint_iff_inf_le.mp (Rgrp_disjoint_Qgrp h hn hnz)) ⟨hfR, hfQ⟩)

theorem Fbar_iso (h : Setting25 G t z z₁ ι zv R0 F) (hn : n ∈ normalizer (ι.range : Set G))
    (hnz : n * z₁ * n⁻¹ = z) : Nonempty (↥(Fbar h n) ≃* alternatingGroup (Fin 5)) := by
  let φ : ↥(Fconj n F) →* ↥(Xgrp h) :=
    (rho0 h).rangeRestrict.comp (Subgroup.inclusion (Fconj_le_Ngrp h hn hnz))
  have hφ_inj : Function.Injective φ := by
    intro a b hab
    have h1 : φ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : rho0 h ((Subgroup.inclusion (Fconj_le_Ngrp h hn hnz)) (a * b⁻¹)) = 1 := by
      have := congrArg Subtype.val h1
      simpa [φ] using this
    have hf : (((a * b⁻¹ : ↥(Fconj n F)) : G)) ∈ Fconj n F := (a * b⁻¹).2
    have h3 : rho0 h ⟨((a * b⁻¹ : ↥(Fconj n F)) : G), Fconj_le_Ngrp h hn hnz hf⟩ = 1 :=
      h2
    have h4 : ((a * b⁻¹ : ↥(Fconj n F)) : G) = 1 := rho0_injOn_Fconj h hn hnz hf h3
    apply Subtype.ext
    have hmul : (a : G) * (b : G)⁻¹ = 1 := by simpa using h4
    exact mul_inv_eq_one.mp hmul
  have hrange : φ.range = Fbar h n := by
    ext x
    rw [MonoidHom.mem_range, mem_Fbar_iff h hn hnz]
    constructor
    · rintro ⟨a, hax⟩
      exact ⟨(a : G), a.2, hax⟩
    · rintro ⟨f, hf, hfx⟩
      exact ⟨⟨f, hf⟩, hfx⟩
  obtain ⟨e⟩ := Fconj_equiv (n := n) h
  exact ⟨((MonoidHom.ofInjective hφ_inj).trans (MulEquiv.subgroupCongr hrange)).symm.trans e⟩

theorem vbar_mul_self (h : Setting25 G t z z₁ ι zv R0 F) (hn : n ∈ normalizer (ι.range : Set G)) :
    vbar h hn * vbar h hn = 1 := by
  have h1 : (⟨n * t * n⁻¹, conj_t_mem_Ngrp h hn⟩ : ↥(Ngrp h)) *
      ⟨n * t * n⁻¹, conj_t_mem_Ngrp h hn⟩ = 1 := by
    apply Subtype.ext
    show (n * t * n⁻¹) * (n * t * n⁻¹) = 1
    rw [← pow_two, conj_t_sq h]
  change (rho0 h).rangeRestrict ⟨n * t * n⁻¹, conj_t_mem_Ngrp h hn⟩ *
      (rho0 h).rangeRestrict ⟨n * t * n⁻¹, conj_t_mem_Ngrp h hn⟩ = 1
  rw [← map_mul, h1, map_one]

theorem vbar_ne_one (h : Setting25 G t z z₁ ι zv R0 F) (hn : n ∈ normalizer (ι.range : Set G))
    (hnz : n * z₁ * n⁻¹ = z) : vbar h hn ≠ 1 := by
  intro h1
  have h2 : rho0 h ⟨n * t * n⁻¹, conj_t_mem_Ngrp h hn⟩ = 1 := by
    have := congrArg Subtype.val h1
    rw [vbar] at this
    simpa using this
  have hR : n * t * n⁻¹ ∈ Rgrp h := (rho0_eq_one_iff h _).mp h2
  have hmem : n * t * n⁻¹ ∈ Rgrp h ⊓ ι.range := ⟨hR, conj_t_mem_range h hn⟩
  rw [Rgrp_inf_range h] at hmem
  exact conj_t_not_mem_Cgrp h hn hnz hmem

theorem Fbar_comm (h : Setting25 G t z z₁ ι zv R0 F) (hn : n ∈ normalizer (ι.range : Set G))
    (hnz : n * z₁ * n⁻¹ = z) : ∀ f ∈ Fbar h n, f * vbar h hn = vbar h hn * f := by
  intro x hx
  rw [mem_Fbar_iff h hn hnz] at hx
  obtain ⟨f, hf, rfl⟩ := hx
  rw [vbar]
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  show f * (n * t * n⁻¹) = (n * t * n⁻¹) * f
  exact (conj_t_comm_Fconj h hf).symm

theorem Kbar_le_sup (h : Setting25 G t z z₁ ι zv R0 F) (hn : n ∈ normalizer (ι.range : Set G))
    (hnz : n * z₁ * n⁻¹ = z) {g : ↥(Ngrp h)} (hg : (g : G) ∈ Kgrp ι z) :
    (rho0 h).rangeRestrict g ∈ Fbar h n ⊔ zpowers (vbar h hn) := by
  let S : Subgroup ↥(Ngrp h) :=
    (Fbar h n ⊔ zpowers (vbar h hn)).comap (rho0 h).rangeRestrict
  have hR : Rgrp h ≤ S.map (Ngrp h).subtype := by
    intro x hx
    rw [Subgroup.mem_map]
    refine ⟨⟨x, Rgrp_le_Ngrp h hx⟩, ?_, rfl⟩
    change (rho0 h).rangeRestrict ⟨x, Rgrp_le_Ngrp h hx⟩ ∈
      Fbar h n ⊔ zpowers (vbar h hn)
    rw [rangeRestrict_eq_one_of_mem_Rgrp h hx]
    exact Subgroup.mem_sup_left (Subgroup.one_mem _)
  have hQ : Qgrp h n ≤ S.map (Ngrp h).subtype := by
    intro x hx
    obtain ⟨a, ha, f, hf, rfl⟩ := (mem_Qgrp h).mp hx
    rw [Subgroup.mem_map]
    refine ⟨⟨a * f, Qgrp_le_Ngrp h hn hnz hx⟩, ?_, rfl⟩
    change (rho0 h).rangeRestrict ⟨a * f, Qgrp_le_Ngrp h hn hnz hx⟩ ∈
      Fbar h n ⊔ zpowers (vbar h hn)
    have haN : a ∈ Ngrp h :=
      Kgrp_le_Ngrp h (Subgroup.zpowers_le.mpr (Setting25.range_le_K h (conj_t_mem_range h hn)) ha)
    have hfN : f ∈ Ngrp h := Fconj_le_Ngrp h hn hnz hf
    have hsub : (⟨a * f, Qgrp_le_Ngrp h hn hnz hx⟩ : ↥(Ngrp h)) =
        (⟨a, haN⟩ : ↥(Ngrp h)) * ⟨f, hfN⟩ := by
      apply Subtype.ext
      rfl
    rw [sup_comm (Fbar h n) (zpowers (vbar h hn)), hsub, map_mul]
    apply Subgroup.mul_mem_sup
    · obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hEq : (⟨a, haN⟩ : ↥(Ngrp h)) =
          (⟨n * t * n⁻¹, conj_t_mem_Ngrp h hn⟩ : ↥(Ngrp h)) ^ e := by
        apply Subtype.ext
        rw [Subgroup.coe_zpow]
        exact he.symm
      rw [hEq, map_zpow]
      exact Subgroup.zpow_mem_zpowers (vbar h hn) e
    · exact (mem_Fbar_iff h hn hnz).mpr ⟨f, hf, rfl⟩
  have hK : Kgrp ι z ≤ S.map (Ngrp h).subtype := by
    rw [← Rgrp_sup_Qgrp h hn hnz]
    exact sup_le hR hQ
  have hgS : (g : G) ∈ S.map (Ngrp h).subtype := hK hg
  rw [Subgroup.mem_map] at hgS
  obtain ⟨s, hs, hsg⟩ := hgS
  have hsg' : s = g := Subtype.ext hsg
  rw [hsg'] at hs
  exact hs

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
