module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.GStab2
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.GCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210Inputs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA CFSG.EvenSporadicStandard.HNRecog
  CFSG.RankThree.Literature.FSmith

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G} {n : G}

theorem map_NVgrp_eq_Pgrp (h : Setting25 G t z z₁ ι zv R0 F) (hzt : ¬ IsConj t z)
    (htz : IsConj t (t * z)) :
    ((NVgrp t z).subgroupOf (Ngrp h)).map (rho0 h).rangeRestrict = Pgrp h := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    rw [Subgroup.mem_subgroupOf] at hg
    obtain ⟨-, hgt⟩ := (mem_normalizer_V_iff_mem_normalizer_Rgrp h hzt htz).mp hg
    apply mem_Pgrp_of_stab h hzt htz
    have hkey : ((rhoX h ((rho0 h).rangeRestrict g) : Wsp h ≃ₗ[ZMod 2] Wsp h)) =
        ((rho0 h g : TauCeti.QuadraticMap.orthogonalGroup (qW h)) :
          Wsp h ≃ₗ[ZMod 2] Wsp h) := rfl
    rw [hkey, show wvec h = toW h t (Setting25.t_mem_Rgrp h) from rfl,
      rho0_toW h g (Setting25.t_mem_Rgrp h)]
    exact (toW_eq_toW_iff h (conj_mem_Rgrp h g.2 (Setting25.t_mem_Rgrp h))
      (Setting25.t_mem_Rgrp h)).2 (by
        rcases hgt with hgt | hgt
        · rw [hgt]; simp
        · rw [hgt]
          have h2 : t * z * t⁻¹ = z := by rw [h.t_mul_z_comm]; group
          rw [h2]; exact Subgroup.mem_zpowers z)
  · intro hx
    rw [Pgrp, Subgroup.mem_map] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    rw [Subgroup.mem_subgroupOf] at hc
    have hct : (c : G) * t = t * (c : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).1
    have hcz : (c : G) * z = z * (c : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2
    have hczc : (c : G) * z * (c : G)⁻¹ = z := mul_inv_eq_iff_eq_mul.mpr hcz
    have hmem : (c : G) ∈ NVgrp t z :=
      mem_normalizer_V_of_conj h.t_sq h.z_sq h.t_mul_z_comm hczc
        (Or.inl (mul_inv_eq_iff_eq_mul.mpr hct))
    rw [Subgroup.mem_map]
    exact ⟨c, Subgroup.mem_subgroupOf.mpr hmem, rfl⟩

theorem mem_Rgrp_of_comm_mem_zpowers (h : Setting25 G t z z₁ ι zv R0 F) {m : G}
    (hm : m ∈ Ngrp h) (H : ∀ x ∈ Rgrp h, m * x * m⁻¹ * x⁻¹ ∈ zpowers z) : m ∈ Rgrp h := by
  rw [← rho0_eq_one_iff h ⟨m, hm⟩]
  refine Subtype.ext ?_
  apply LinearEquiv.ext
  intro w
  obtain ⟨x, hx, rfl⟩ := toW_surjective h w
  rw [rho0_toW h ⟨m, hm⟩ hx]
  simp only [LinearEquiv.coe_one, id_eq]
  exact (toW_eq_toW_iff h (conj_mem_Rgrp h hm hx) hx).2 (H x hx)

theorem rangeRestrict_eq_vbar (h : Setting25 G t z z₁ ι zv R0 F)
    (hn : n ∈ normalizer (ι.range : Set G)) (hnz : n * z₁ * n⁻¹ = z) {m : G}
    (hm : m ∈ Ngrp h) (hmA : m ∈ ι.range) (hmR : m ∉ Rgrp h) :
    (rho0 h).rangeRestrict ⟨m, hm⟩ = vbar h hn := by
  have hv : n * t * n⁻¹ ∈ Ngrp h := conj_t_mem_Ngrp h hn
  rcases mem_Cgrp_or_mul_conj_t_mem_Cgrp h hn hnz hmA with hC | hCv
  · exact absurd (Cgrp_le_Rgrp h hC) hmR
  · have hmvR : m * (n * t * n⁻¹) ∈ Rgrp h := Cgrp_le_Rgrp h hCv
    have h1 : (rho0 h).rangeRestrict
        ⟨m * (n * t * n⁻¹), Rgrp_le_Ngrp h hmvR⟩ = 1 := by
      apply Subtype.ext
      simpa using (rho0_eq_one_iff h
        ⟨m * (n * t * n⁻¹), Rgrp_le_Ngrp h hmvR⟩).mpr hmvR
    have hprod : ((⟨m, hm⟩ : ↥(Ngrp h)) * ⟨n * t * n⁻¹, hv⟩) =
        (⟨m * (n * t * n⁻¹), Rgrp_le_Ngrp h hmvR⟩ : ↥(Ngrp h)) :=
      Subtype.ext rfl
    have h2 : (rho0 h).rangeRestrict ⟨m, hm⟩ * vbar h hn = 1 := by
      have h2' : (rho0 h).rangeRestrict ⟨m, hm⟩ *
          (rho0 h).rangeRestrict ⟨n * t * n⁻¹, hv⟩ = 1 := by
        rw [← map_mul, hprod, h1]
      exact h2'
    rw [mul_eq_one_iff_eq_inv.mp h2,
      inv_eq_of_mul_eq_one_right (vbar_mul_self h hn)]

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
