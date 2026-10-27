module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210QHom
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210QOuterG
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NMAComp2

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G} (h : Setting25 G t z z₁ ι zv R0 F)
  {φ : ↥(normalizer (Rgrp h : Set G)) →* A5WrTwo}

private theorem z_mem_Cgrp (h : Setting25 G t z z₁ ι zv R0 F) : z ∈ Cgrp ι zv := by
  rw [← h.coord_z]
  exact (coordElt_mem_Cgrp h.injective_ι).mpr (bil_self zv)

private theorem card_ker_piq_inf_Cgrp (h : Setting25 G t z z₁ ι zv R0 F) :
    Nat.card ↥((piq z).ker ⊓ (Cgrp ι zv).subgroupOf (Mgrp z)) = 2 := by
  have hker_le : (piq z).ker ≤ (Cgrp ι zv).subgroupOf (Mgrp z) := by
    rw [ker_piq z]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      (Subgroup.zpowers_le.mpr (z_mem_Cgrp h) (Subgroup.mem_subgroupOf.mp hx))
  rw [inf_of_le_left hker_le, ker_piq z]
  have hzM : zpowers z ≤ Mgrp z :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl z))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzM).toEquiv]
  haveI : Fintype G := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card, Fintype.card_zpowers]
  exact orderOf_eq_prime h.z_sq h.z_ne_one

theorem card_Aq_inf_centralizer_le {v : ↥(Mgrp z)} (hv : (v : G) ∈ ι.range)
    (hvR : (v : G) ∉ Rgrp h) :
    Nat.card ↥(Aq h ⊓ centralizer ({piq z v} : Set (Xq z))) ≤ 16 := by
  classical
  let CM : Subgroup ↥(Mgrp z) := (Cgrp ι zv).subgroupOf (Mgrp z)
  have hC_le_M : Cgrp ι zv ≤ Mgrp z := (Cgrp_le_Rgrp h).trans (Rgrp_le_Mgrp h)
  have hcard_CM : Nat.card ↥CM = 32 := by
    have he : Nat.card ↥CM = Nat.card ↥(Cgrp ι zv) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC_le_M).toEquiv
    rw [he, card_Cgrp h.injective_ι h.zv_ne_zero]
  have hcard_ker : Nat.card ↥((piq z).ker ⊓ CM) = 2 := by
    simpa only [CM] using card_ker_piq_inf_Cgrp h
  have hrel : Nat.card (CM.map (piq z)) = (piq z).ker.relIndex CM :=
    (Subgroup.relIndex_ker CM (piq z)).symm
  have hcard_Cb : Nat.card (CM.map (piq z)) = 16 := by
    have key : Nat.card (CM.map (piq z)) * 2 = 32 := by
      calc Nat.card (CM.map (piq z)) * 2
          = (piq z).ker.relIndex CM * Nat.card ↥((piq z).ker ⊓ CM) := by
            rw [hrel, ← hcard_ker]
        _ = Nat.card ↥CM := Subgroup.relIndex_mul_card (piq z).ker CM
        _ = 32 := hcard_CM
    omega
  have hle : Aq h ⊓ centralizer ({piq z v} : Set (Xq z)) ≤ CM.map (piq z) := by
    intro a ha
    obtain ⟨haA, hac⟩ := Subgroup.mem_inf.mp ha
    rw [Aq] at haA
    obtain ⟨x, hxCM, hxa⟩ := Subgroup.mem_map.mp haA
    have hxR : (x : G) ∈ Rgrp h := Subgroup.mem_subgroupOf.mp hxCM
    have hvx : piq z v * piq z x = piq z x * piq z v := by
      have h := (Subgroup.mem_centralizer_iff.mp hac) (piq z v) (Set.mem_singleton _)
      rwa [← hxa] at h
    have hker : x * v * x⁻¹ * v⁻¹ ∈ (piq z).ker := by
      rw [MonoidHom.mem_ker]
      have h1 : piq z x * piq z v = piq z v * piq z x := hvx.symm
      calc piq z (x * v * x⁻¹ * v⁻¹)
          = piq z x * piq z v * (piq z x)⁻¹ * (piq z v)⁻¹ := by
            simp only [map_mul, map_inv]
        _ = 1 := by rw [h1]; group
    have hc : (x : G) * (v : G) * (x : G)⁻¹ * (v : G)⁻¹ ∈ zpowers z := by
      have h2 : x * v * x⁻¹ * v⁻¹ ∈ (zpowers z).subgroupOf (Mgrp z) := by
        rw [← ker_piq z]; exact hker
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using (Subgroup.mem_subgroupOf.mp h2)
    have hxC : (x : G) ∈ Cgrp ι zv := mem_Cgrp_of_comm_mem_zpowers h hv hvR hxR hc
    exact Subgroup.mem_map.mpr ⟨x, Subgroup.mem_subgroupOf.mpr hxC, hxa⟩
  calc Nat.card ↥(Aq h ⊓ centralizer ({piq z v} : Set (Xq z)))
      ≤ Nat.card (CM.map (piq z)) := Subgroup.card_le_of_le hle
    _ = 16 := hcard_Cb

theorem outer_Aq (hs : Lemma27Spec h φ) :
    ∃ v : ↥(normalizer (Aq h : Set (Xq z))), (v : Xq z) ∉ Aq h ∧ (v : Xq z) * (v : Xq z) = 1 ∧
      psiq h hs v ∉ commutator A5WrTwo ∧
      Nat.card ↥(Aq h ⊓ centralizer ({(v : Xq z)} : Set (Xq z))) ≤ 16 := by
  classical
  obtain ⟨n, hn, hnz⟩ := Setting25.exists_n_z₁ h
  let w : G := n * t * n⁻¹
  have hw_range : w ∈ ι.range := conj_t_mem_range h hn
  have hwQ : w ∈ Qgrp h n :=
    (mem_Qgrp h).mpr ⟨w, Subgroup.mem_zpowers w, 1, Subgroup.one_mem _, (mul_one w).symm⟩
  have hwK : w ∈ Kgrp ι z := Qgrp_le_K h hn hnz hwQ
  have hwN : w ∈ normalizer (Rgrp h : Set G) := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact Rgrp_conj h hwK hx
    · intro hx
      have h' : w⁻¹ * (w * x * w⁻¹) * (w⁻¹)⁻¹ ∈ Rgrp h :=
        Rgrp_conj h (inv_mem hwK) hx
      have heq : w⁻¹ * (w * x * w⁻¹) * (w⁻¹)⁻¹ = x := by group
      rwa [heq] at h'
  have hwR : w ∉ Rgrp h := by
    intro hwR
    have hbot : w ∈ (⊥ : Subgroup G) :=
      (disjoint_iff_inf_le.mp (Rgrp_disjoint_Qgrp h hn hnz)) ⟨hwR, hwQ⟩
    have hw1 : w = 1 := Subgroup.mem_bot.mp hbot
    exact conj_t_not_mem_Cgrp h hn hnz (by
      rw [show n * t * n⁻¹ = 1 from hw1]
      exact Subgroup.one_mem _)
  refine ⟨piN h ⟨w, hwN⟩, ?_, ?_, ?_, ?_⟩
  · rw [piN_val]
    exact (mem_Aq_iff h ⟨w, normalizer_Rgrp_le_Mgrp h hwN⟩).not.mpr (by simpa using hwR)
  · rw [piN_val]
    have hww : (⟨w, normalizer_Rgrp_le_Mgrp h hwN⟩ : ↥(Mgrp z)) *
        ⟨w, normalizer_Rgrp_le_Mgrp h hwN⟩ = 1 := by
      apply Subtype.ext
      show w * w = 1
      rw [← pow_two]
      exact conj_t_sq h
    calc piq z ⟨w, normalizer_Rgrp_le_Mgrp h hwN⟩ * piq z ⟨w, normalizer_Rgrp_le_Mgrp h hwN⟩
        = piq z (⟨w, normalizer_Rgrp_le_Mgrp h hwN⟩ * ⟨w, normalizer_Rgrp_le_Mgrp h hwN⟩) :=
          (map_mul (piq z) _ _).symm
      _ = piq z 1 := by rw [hww]
      _ = 1 := map_one (piq z)
  · rw [psiq_piN h hs ⟨w, hwN⟩]
    exact hs.outer w hwN hw_range hwR
  · rw [piN_val]
    exact card_Aq_inf_centralizer_le h hw_range hwR

end CFSG.EvenSporadicStandard.HNRecog.Harada
