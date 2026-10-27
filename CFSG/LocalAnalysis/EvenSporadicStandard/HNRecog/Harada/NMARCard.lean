module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NMAR
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.ZStabCard

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G}

private theorem zmod2_eq_one_of_ne_zero {c : ZMod 2} (h : c ≠ 0) : c = 1 := by
  have hval : c.val ≠ 0 := fun hv => h ((ZMod.val_eq_zero c).1 hv)
  have h1 : c.val = 1 := by have := ZMod.val_lt c; omega
  exact (ZMod.val_eq_one (by norm_num : 1 < 2) c).1 h1

private theorem zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  by_cases h : c = 0
  · exact Or.inl h
  · exact Or.inr (zmod2_eq_one_of_ne_zero h)

theorem actImage_Rgrp (h : Setting25 G t z z₁ ι zv R0 F) :
    actImage ι (Rgrp h) = EichU zv := by
  ext g
  constructor
  · rintro ⟨x, hx, hg⟩
    obtain ⟨u, hu⟩ := Rgrp_eichActs h hx
    have huniq : g = eichPerm zv u hu.1 := Acts.unique h.injective_ι hg hu.acts
    rw [huniq]
    exact eichPerm_mem_EichU hu.1
  · intro hg
    obtain ⟨u, hu, hgu⟩ := mem_EichU.mp hg
    obtain ⟨x, hx, hxacts⟩ := exists_mem_Rgrp h hu
    exact ⟨x, hx, fun v => by rw [hxacts.2 v, hgu v]⟩

theorem card_Rgrp (h : Setting25 G t z z₁ ι zv R0 F) : Nat.card (Rgrp h) = 2 ^ 9 := by
  have hP : Rgrp h ≤ normalizer (ι.range : Set G) :=
    (Rgrp_le_K h).trans inf_le_left
  have hcard := card_eq_card_inf_mul_card_actImage h.injective_ι h.centralizer_le hP
  rw [hcard, Rgrp_inf_range h, actImage_Rgrp h,
    card_Cgrp h.injective_ι h.zv_ne_zero, card_EichU h.hD2.qm_zv h.zv_ne_zero]
  norm_num

theorem Rgrp_conj_t (h : Setting25 G t z z₁ ι zv R0 F) {x : G} (hx : x ∈ Rgrp h) :
    x * t * x⁻¹ = t ∨ x * t * x⁻¹ = t * z := by
  obtain ⟨u, hu⟩ := Rgrp_eichActs h hx
  have htv : coordElt ι tv = t := h.ι_tv
  have hzv : coordElt ι zv = z := h.coord_z
  have hbil : bil tv zv = 0 := h.bil_tv_zv
  have key : x * t * x⁻¹ = coordElt ι (eichF zv u tv) := by
    rw [← htv]
    exact hu.2 tv
  have heich : eichF zv u tv = tv + (bil tv u) • zv := by
    simp only [eichF, hbil, zero_smul, mul_zero, add_zero]
  rcases zmod2_eq_zero_or_one (bil tv u) with hb | hb
  · left
    rw [key, heich, hb, zero_smul, add_zero, htv]
  · right
    rw [key, heich, hb, one_smul, coordElt_add, htv, hzv]

end CFSG.EvenSporadicStandard.HNRecog.Harada
