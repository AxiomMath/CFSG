module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NMAR

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G} (h : Setting25 G t z z₁ ι zv R0 F)

private theorem v6_add_self (v : V6) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

private lemma coordElt_injective (hι : Function.Injective ι) :
    Function.Injective (coordElt ι) := by
  intro u v huv
  have h : Multiplicative.ofAdd u = Multiplicative.ofAdd v := hι huv
  simpa using congrArg Multiplicative.toAdd h

private theorem zmod2_eq_one_of_ne_zero {c : ZMod 2} (h : c ≠ 0) : c = 1 := by
  have hval : c.val ≠ 0 := fun hv => h ((ZMod.val_eq_zero c).1 hv)
  have h1 : c.val = 1 := by have := ZMod.val_lt c; omega
  exact (ZMod.val_eq_one (by norm_num : 1 < 2) c).1 h1

private theorem zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  by_cases h : c = 0
  · exact Or.inl h
  · exact Or.inr (zmod2_eq_one_of_ne_zero h)

private theorem mem_zpowers_two {z y : G} (hz : z ^ 2 = 1) (hzne : z ≠ 1)
    (hy : y ∈ zpowers z) : y = 1 ∨ y = z := by
  classical
  have hord : orderOf z = 2 := orderOf_eq_prime (p := 2) hz hzne
  rw [mem_zpowers_iff_mem_range_orderOf, hord, Finset.mem_image] at hy
  obtain ⟨n, hn, hny⟩ := hy
  rw [Finset.mem_range] at hn
  have hn' : n = 0 ∨ n = 1 := by omega
  rcases hn' with h | h
  · left; rw [← hny, h]; simp
  · right; rw [← hny, h]; simp

theorem mem_Cgrp_of_comm_mem_zpowers {v : G} (hv : v ∈ ι.range) (hvR : v ∉ Rgrp h) {x : G}
    (hx : x ∈ Rgrp h) (hc : x * v * x⁻¹ * v⁻¹ ∈ zpowers z) : x ∈ Cgrp ι zv := by
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hv
  set a : V6 := Multiplicative.toAdd b with ha
  have hca : coordElt ι a = v := by
    rw [ha]
    simpa [coordElt] using hb
  have hba_ne : bil a zv ≠ 0 := by
    intro h0
    exact hvR (Cgrp_le_Rgrp h (mem_Cgrp.mpr ⟨a, h0, hca⟩))
  have hba : bil a zv = 1 := zmod2_eq_one_of_ne_zero hba_ne
  obtain ⟨u, hx_eich⟩ := Rgrp_eichActs h hx
  have hxconj : x * v * x⁻¹ = coordElt ι (eichF zv u a) := by
    rw [← hca, hx_eich.2 a]
  have hv_inv : v⁻¹ = coordElt ι a := by
    have hvv : coordElt ι a * coordElt ι a = 1 := by
      rw [← coordElt_add, v6_add_self a, coordElt_zero]
    rw [← hca]
    exact inv_eq_of_mul_eq_one_right hvv
  have heichF : eichF zv u a = a + u + (bil a u + qm u) • zv := by
    rw [eichF, hba, one_smul, mul_one]
  have hcomm_eq : x * v * x⁻¹ * v⁻¹ = coordElt ι (u + (bil a u + qm u) • zv) := by
    rw [hxconj, hv_inv, ← coordElt_add, heichF]
    congr 1
    rw [show (a + u + (bil a u + qm u) • zv) + a
          = (a + a) + (u + (bil a u + qm u) • zv) by abel,
      v6_add_self a, zero_add]
  have hmain : coordElt ι (u + (bil a u + qm u) • zv) ∈ zpowers z := by
    rw [← hcomm_eq]
    exact hc
  have hzero_or : u + (bil a u + qm u) • zv = 0 ∨ u + (bil a u + qm u) • zv = zv := by
    rcases mem_zpowers_two h.z_sq h.z_ne_one hmain with h1 | h1
    · left
      apply coordElt_injective h.injective_ι
      rw [h1, coordElt_zero]
    · right
      apply coordElt_injective h.injective_ι
      rw [h1, h.coord_z]
  have hu : u = 0 ∨ u = zv := by
    rcases hzero_or with h0 | h1
    · rcases zmod2_eq_zero_or_one (bil a u + qm u) with hc0 | hc1
      · left
        rw [hc0, zero_smul, add_zero] at h0
        exact h0
      · right
        rw [hc1, one_smul] at h0
        have h2 : u + zv + zv = 0 + zv := by rw [h0]
        rwa [add_assoc, v6_add_self zv, add_zero, zero_add] at h2
    · rcases zmod2_eq_zero_or_one (bil a u + qm u) with hc0 | hc1
      · right
        rw [hc0, zero_smul, add_zero] at h1
        exact h1
      · left
        rw [hc1, one_smul] at h1
        exact add_right_cancel (h1.trans (zero_add zv).symm)
  have heich_id : ∀ y : V6, eichF zv u y = y := by
    intro y
    rcases hu with hu0 | huzv
    · rw [hu0]; exact eichF_zero zv y
    · rw [huzv]
      have hadd := @eichF_add_w zv 0 h.hD2.qm_zv (bil_zero_left zv) y
      rw [zero_add, eichF_zero] at hadd
      exact hadd
  have hx_comm : ∀ g ∈ ι.range, x * g = g * x := by
    rintro g ⟨b', hb'⟩
    have hcb' : coordElt ι (Multiplicative.toAdd b') = g := by
      simpa [coordElt] using hb'
    have hstep := hx_eich.2 (Multiplicative.toAdd b')
    rw [heich_id (Multiplicative.toAdd b')] at hstep
    rw [hcb'] at hstep
    exact mul_inv_eq_iff_eq_mul.mp hstep
  have hxcent : x ∈ centralizer (ι.range : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact (hx_comm g hg).symm
  have hxr : x ∈ ι.range := h.centralizer_le hxcent
  rw [← Rgrp_inf_range h]
  exact ⟨hx, hxr⟩

end CFSG.EvenSporadicStandard.HNRecog.Harada
