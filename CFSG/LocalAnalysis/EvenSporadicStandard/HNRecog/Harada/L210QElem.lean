module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210QDefs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.Open CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G} (h : Setting25 G t z z₁ ι zv R0 F)

private theorem piq_commutator_mem_ker (h : Setting25 G t z z₁ ι zv R0 F)
    {x y : ↥(Mgrp z)} (hx : (x : G) ∈ Rgrp h) (hy : (y : G) ∈ Rgrp h) :
    x * y * x⁻¹ * y⁻¹ ∈ (piq z).ker := by
  rw [ker_piq z]
  exact Subgroup.mem_subgroupOf.mpr
    (by simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using Rgrp_comm h hx hy)

private theorem piq_mul_comm (h : Setting25 G t z z₁ ι zv R0 F) {x y : ↥(Mgrp z)}
    (hx : (x : G) ∈ Rgrp h) (hy : (y : G) ∈ Rgrp h) :
    piq z x * piq z y = piq z y * piq z x := by
  have hker := piq_commutator_mem_ker h hx hy
  calc piq z x * piq z y
      = piq z (x * y) := (map_mul (piq z) x y).symm
    _ = piq z ((x * y * x⁻¹ * y⁻¹) * (y * x)) := by
          rw [show (x * y * x⁻¹ * y⁻¹) * (y * x) = x * y by group]
    _ = piq z (x * y * x⁻¹ * y⁻¹) * piq z (y * x) := map_mul (piq z) _ _
    _ = 1 * piq z (y * x) := by rw [MonoidHom.mem_ker.mp hker]
    _ = piq z (y * x) := one_mul _
    _ = piq z y * piq z x := map_mul (piq z) y x

private theorem piq_sq_eq_one (h : Setting25 G t z z₁ ι zv R0 F) {x : ↥(Mgrp z)}
    (hx : (x : G) ∈ Rgrp h) : piq z (x ^ 2) = 1 := by
  apply MonoidHom.mem_ker.mp
  rw [ker_piq z]
  exact Subgroup.mem_subgroupOf.mpr
    (by simpa only [Subgroup.coe_pow] using Rgrp_sq h hx)

theorem Aq_elemAb : IsElemAbelian 2 (Aq h) := by
  refine ⟨?_, ?_⟩
  · refine IsMulCommutative.of_comm fun a b => Subtype.ext ?_
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp b.2
    simp only [Subgroup.coe_mul]
    rw [← hxa, ← hyb]
    exact piq_mul_comm h (Subgroup.mem_subgroupOf.mp hx) (Subgroup.mem_subgroupOf.mp hy)
  · intro a ha
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp ha
    rw [← hxa, ← map_pow]
    exact piq_sq_eq_one h (Subgroup.mem_subgroupOf.mp hx)

theorem card_Aq : Nat.card (Aq h) = 2 ^ 8 := by
  let R_M : Subgroup ↥(Mgrp z) := (Rgrp h).subgroupOf (Mgrp z)
  have hRM : R_M.map (piq z) = Aq h := rfl
  have hker_le : (piq z).ker ≤ R_M := by
    rw [ker_piq z]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      (Subgroup.zpowers_le.mpr (z_mem_Rgrp h) (Subgroup.mem_subgroupOf.mp hx))
  have hker_card : Nat.card ↥((piq z).ker) = 2 := by
    rw [ker_piq z]
    have hle : zpowers z ≤ Mgrp z :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl z))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    haveI : Fintype G := Fintype.ofFinite G
    rw [Nat.card_eq_fintype_card, Fintype.card_zpowers]
    exact orderOf_eq_prime h.z_sq h.z_ne_one
  have hRleM : Rgrp h ≤ Mgrp z :=
    (Rgrp_le_K h).trans (by rw [Kgrp]; exact inf_le_right)
  have hRM_card : Nat.card ↥R_M = 2 ^ 9 := by
    have he : Nat.card ↥R_M = Nat.card ↥(Rgrp h) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRleM).toEquiv
    rw [he, card_Rgrp h]
  have hrel : Nat.card (Aq h) = (piq z).ker.relIndex R_M := by
    rw [Subgroup.relIndex_ker R_M (piq z), hRM]
  have key : Nat.card (Aq h) * 2 = 2 ^ 9 := by
    calc Nat.card (Aq h) * 2
        = (piq z).ker.relIndex R_M * Nat.card ↥((piq z).ker ⊓ R_M) := by
          rw [hrel, inf_of_le_left hker_le, hker_card]
      _ = Nat.card ↥R_M := Subgroup.relIndex_mul_card (piq z).ker R_M
      _ = 2 ^ 9 := hRM_card
  have h9 : (2 : ℕ) ^ 9 = 512 := by norm_num
  have h8 : (2 : ℕ) ^ 8 = 256 := by norm_num
  rw [h9] at key
  rw [h8]
  omega

end CFSG.EvenSporadicStandard.HNRecog.Harada
