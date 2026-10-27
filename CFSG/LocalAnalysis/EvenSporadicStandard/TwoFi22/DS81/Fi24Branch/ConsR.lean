module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Core4
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.ConsBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.ConsSelf
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CSetup

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {G : Type} [Group G] [Finite G] {E : Subgroup G} {t z : G}

theorem Rg_le_Cz (c : Core1 E t z) : Rg t z ≤ Cz z := (Rg_le_Jg t z).trans c.jr.J_le_C

theorem center_Rg_map (c : Core1 E t z) :
    (center ↥(Rg t z)).map (Rg t z).subtype = zpowers z := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine (c.jr.center_R (y : G) y.2).mp ?_
    intro a ha
    have h := (Subgroup.mem_center_iff.mp hy) (⟨a, ha⟩ : ↥(Rg t z))
    exact (congrArg Subtype.val h).symm
  · intro hx
    have hxR : x ∈ Rg t z := (Subgroup.zpowers_le.mpr (c.jr.V_le_R z_mem_Vtz)) hx
    refine ⟨⟨x, hxR⟩, ?_, rfl⟩
    refine Subgroup.mem_center_iff.mpr ?_
    intro y
    apply Subtype.ext
    exact ((c.jr.center_R x hxR).mpr hx (y : G) y.2).symm

theorem rData (c : Core4 E t z) :
    RData (czInv z c.klein.z_sq c.klein.z_ne) ((Rg t z).subgroupOf (Cz z)) := by
  let C := ↥(Cz z)
  let cI : CInv C := czInv z c.klein.z_sq c.klein.z_ne
  let R' : Subgroup C := (Rg t z).subgroupOf (Cz z)
  have hc1 : Core1 E t z := c.toCore3.toCore2.toCore1
  have hRC : Rg t z ≤ Cz z := Rg_le_Cz hc1
  have hzR : z ∈ Rg t z := c.jr.V_le_R z_mem_Vtz
  have hzC : cI.z ∈ R' := by
    rw [Subgroup.mem_subgroupOf]
    exact hzR
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hzC
  · rw [card_subgroupOf' hRC, c.jr.card_R]
  · intro x hx
    have hxG : (x : G) ∈ Rg t z := Subgroup.mem_subgroupOf.mp hx
    have hsq : (x : G) ^ 2 ∈ Phi2 (Rg t z) :=
      Subgroup.mem_sup_right (Subgroup.subset_closure ⟨(x : G), hxG, rfl⟩)
    rw [c.extra.phi_eq] at hsq
    exact (mem_zpowers_czInv z c.klein.z_sq c.klein.z_ne (x ^ 2)).mpr (by simpa using hsq)
  · intro x hx y hy
    have hxG : (x : G) ∈ Rg t z := Subgroup.mem_subgroupOf.mp hx
    have hyG : (y : G) ∈ Rg t z := Subgroup.mem_subgroupOf.mp hy
    have hcomm : (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ ∈ Phi2 (Rg t z) := by
      have h := Subgroup.mem_sup_left
        (S := ⁅Rg t z, Rg t z⁆)
        (T := closure {w | ∃ v ∈ Rg t z, w = v ^ 2})
        (Subgroup.commutator_mem_commutator hxG hyG)
      simpa [Phi2, commutatorElement_def] using h
    rw [c.extra.phi_eq] at hcomm
    exact (mem_zpowers_czInv z c.klein.z_sq c.klein.z_ne
      (x * y * x⁻¹ * y⁻¹)).mpr (by simpa using hcomm)
  · intro x hx hxcomm
    have hxG : (x : G) ∈ Rg t z := Subgroup.mem_subgroupOf.mp hx
    refine (mem_zpowers_czInv z c.klein.z_sq c.klein.z_ne x).mpr ?_
    refine (c.jr.center_R (x : G) hxG).mp ?_
    intro y hy
    have hy' : (⟨y, hRC hy⟩ : C) ∈ R' := by
      rw [Subgroup.mem_subgroupOf]
      exact hy
    exact congrArg Subtype.val (hxcomm ⟨y, hRC hy⟩ hy')
  · intro g hg
    have hcent : centralizer (Rg t z : Set G) ≤ Rg t z := by
      rw [c.jr.cent_R]
      exact Subgroup.zpowers_le.mpr hzR
    have hR : CFSG.IsExtraspecialPGroup 2 ↥(Rg t z) :=
      (CFSG.isExtraspecialPGroup_iff_isExtraspecial (p := 2)).mpr c.extra.extraspecial
    have hg' : ∀ r ∈ Rg t z,
        (g : G) * r * (g : G)⁻¹ * r⁻¹ ∈ (center ↥(Rg t z)).map (Rg t z).subtype := by
      intro r hr
      have hr' : (⟨r, hRC hr⟩ : C) ∈ R' := by
        rw [Subgroup.mem_subgroupOf]
        exact hr
      have h := hg ⟨r, hRC hr⟩ hr'
      have hmem : (((g : C) * (⟨r, hRC hr⟩ : C) * (g : C)⁻¹ *
        (⟨r, hRC hr⟩ : C)⁻¹ : C) : G) ∈ zpowers z :=
        (mem_zpowers_czInv z c.klein.z_sq c.klein.z_ne _).mp h
      rw [center_Rg_map hc1]
      simpa using hmem
    have hgR : (g : G) ∈ Rg t z := mem_of_commutators_mem_center hR hcent hg'
    rw [Subgroup.mem_subgroupOf]
    exact hgR
  · intro U hzU hUR hUinv
    let U0 : Subgroup G := U.map (Cz z).subtype
    have hzU0 : zpowers z ≤ U0 := by
      refine Subgroup.zpowers_le.mpr ?_
      have hmem : cI.z ∈ U := hzU (Subgroup.mem_zpowers cI.z)
      exact Subgroup.mem_map_of_mem (Cz z).subtype hmem
    have hU0R : U0 ≤ Rg t z := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨u, hu, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (hUR hu)
    have hCNinv : InvUnder (CNz E z) U0 := by
      intro n hn x hx
      rcases Subgroup.mem_map.mp hx with ⟨u, hu, rfl⟩
      have hnC : (⟨n, CNz_le_Cz E z hn⟩ : C) ∈ normalizer (R' : Set C) := by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          rw [Subgroup.mem_subgroupOf] at hy ⊢
          simpa using c.rnorm n hn (y : G) hy
        · intro hy
          rw [Subgroup.mem_subgroupOf] at hy ⊢
          have h := c.rnorm n⁻¹ ((CNz E z).inv_mem hn) (n * (y : G) * n⁻¹) hy
          have h' : n⁻¹ * (n * (y : G) * n⁻¹) * n⁻¹⁻¹ = (y : G) := by group
          rwa [h'] at h
      have h := hUinv ⟨n, CNz_le_Cz E z hn⟩ hnC u hu
      exact Subgroup.mem_map_of_mem (Cz z).subtype h
    have hJinv : InvUnder (Jg t z) U0 := by
      intro j hj x hx
      rcases Subgroup.mem_map.mp hx with ⟨u, hu, rfl⟩
      have hjC : (⟨j, c.jr.J_le_C hj⟩ : C) ∈ normalizer (R' : Set C) := by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          rw [Subgroup.mem_subgroupOf] at hy ⊢
          simpa using c.jr.R_normal j hj (y : G) hy
        · intro hy
          rw [Subgroup.mem_subgroupOf] at hy ⊢
          have h := c.jr.R_normal j⁻¹ ((Jg t z).inv_mem hj) (j * (y : G) * j⁻¹) hy
          have h' : j⁻¹ * (j * (y : G) * j⁻¹) * j⁻¹⁻¹ = (y : G) := by group
          rwa [h'] at h
      have h := hUinv ⟨j, c.jr.J_le_C hj⟩ hjC u hu
      exact Subgroup.mem_map_of_mem (Cz z).subtype h
    have hmapz : (zpowers cI.z).map (Cz z).subtype = zpowers z := by
      rw [MonoidHom.map_zpowers]
      rfl
    rcases c.irred U0 hzU0 hU0R hCNinv hJinv with hU0 | hU0
    · left
      apply Subgroup.map_injective (Cz z).subtype_injective
      have hU : U.map (Cz z).subtype = zpowers z := hU0
      rw [hU, hmapz]
    · right
      apply Subgroup.map_injective (Cz z).subtype_injective
      have hU : U.map (Cz z).subtype = Rg t z := hU0
      rw [hU, Subgroup.map_subgroupOf_eq_of_le hRC]

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
