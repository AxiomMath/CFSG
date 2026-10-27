module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Core
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.ConsBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CSetup

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {G : Type} [Group G] [Finite G] {E : Subgroup G} {t z : G}

theorem Kg_le_Cz (t z : G) : Kg t z ≤ Cz z := fun _ hk => mem_Cz.mpr (mem_Kg.mp hk).2

theorem kDataC (c : Core1 E t z) :
    ∃ Y : Subgroup ↥(Cz z),
      KDataC (czInv z c.klein.z_sq c.klein.z_ne) (⟨t, mem_Cz_of_comm c.klein.comm⟩ : ↥(Cz z))
        ((Rg t z).subgroupOf (Cz z)) ((Jg t z).subgroupOf (Cz z)) ((Kg t z).subgroupOf (Cz z))
        ((OKg t z).subgroupOf (Cz z)) Y := by
  obtain ⟨Y, hYK, hYperf, -, hlat⟩ := c.kdata.perfect
  have hKD : Kg t z ≤ Cz z := Kg_le_Cz t z
  have hOD : OKg t z ≤ Cz z := (OKg_le_Kg t z).trans hKD
  have hYD : Y ≤ Cz z := hYK.trans hKD
  have hVtzD : Vtz t z ≤ Cz z := c.kdata.V_le.trans hOD
  have hzv : (czInv z c.klein.z_sq c.klein.z_ne).z = (⟨z, mem_Cz.mpr rfl⟩ : ↥(Cz z)) := rfl
  refine ⟨Y.subgroupOf (Cz z), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact Kg_le_Jg t z (Subgroup.mem_subgroupOf.mp hx)
  · intro k hk
    apply Subtype.ext
    exact (mem_Kg.mp (Subgroup.mem_subgroupOf.mp hk)).1
  · ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    rw [← Subgroup.mem_inf, c.jr.R_inf_K]
  · rw [card_subgroupOf' hOD, c.kdata.card_OK]
  · rw [hzv, closure_pair_subgroupOf (mem_Cz_of_comm c.klein.comm) (mem_Cz.mpr rfl)]
    exact Subgroup.subgroupOf_mono (Cz z) c.kdata.V_le
  · rw [hzv, closure_pair_subgroupOf (mem_Cz_of_comm c.klein.comm) (mem_Cz.mpr rfl)]
    change Nat.card ↥((Vtz t z).subgroupOf (Cz z)) = 4
    rw [card_subgroupOf' hVtzD, card_Vtz c.klein]
  · exact Subgroup.subgroupOf_mono (Cz z) hYK
  · exact perfect_subgroupOf hYD hYperf
  · intro U hVU hUO hInv
    let U₀ : Subgroup G := U.map (Cz z).subtype
    have hVU' : (Vtz t z).subgroupOf (Cz z) ≤ U := by
      change (closure {t, z}).subgroupOf (Cz z) ≤ U
      rw [← closure_pair_subgroupOf (mem_Cz_of_comm c.klein.comm) (mem_Cz.mpr rfl)]
      exact hVU
    have hVU0 : Vtz t z ≤ U₀ := by
      have h := Subgroup.map_mono (f := (Cz z).subtype) hVU'
      rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVtzD] at h
    have hU0O : U₀ ≤ OKg t z := by
      have h := Subgroup.map_mono (f := (Cz z).subtype) hUO
      rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hOD] at h
    have hInv0 : InvUnder Y U₀ := by
      intro y hy u hu
      rcases hu with ⟨u', hu'U, hval⟩
      subst hval
      exact ⟨(⟨y, hYD hy⟩ : ↥(Cz z)) * u' * (⟨y, hYD hy⟩ : ↥(Cz z))⁻¹,
        hInv ⟨y, hYD hy⟩ (Subgroup.mem_subgroupOf.mpr hy) u' hu'U, rfl⟩
    have h := hlat U₀ hVU0 hU0O hInv0
    rwa [Subgroup.card_subtype (Cz z) U] at h
  · obtain ⟨X, hX, π, hπs, hπk, hXU⟩ := c.kdata.quot
    letI : Group X := hX
    obtain ⟨π', hπ's, hπ'k⟩ := quot_subgroupOf hKD π hπs hπk
    exact ⟨X, hX, π', hπ's, hπ'k, hXU⟩

theorem y0Data (c : Core0 E t z) : ∃ Y0 : Subgroup ↥(Cz z), Y0Data Y0 := by
  obtain ⟨Y, hYN, hYp, hYc⟩ := c.cocode.exists_perfect
  have hYD : Y ≤ Cz z := hYN.trans (CNz_le_Cz E z)
  refine ⟨Y.subgroupOf (Cz z), ?_, ?_⟩
  · exact perfect_subgroupOf hYD hYp
  · rw [card_subgroupOf' hYD, hYc]

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
