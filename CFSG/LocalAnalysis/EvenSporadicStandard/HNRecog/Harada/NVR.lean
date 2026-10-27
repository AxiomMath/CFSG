module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NVD
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NMARCard

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G}

theorem Rgrp_le_normalizer_V (h : Setting25 G t z z₁ ι zv R0 F) :
    Rgrp h ≤ normalizer ((zpowers t ⊔ zpowers z : Subgroup G) : Set G) := by
  intro x hx
  have hxK : x ∈ Kgrp ι z := Rgrp_le_K h hx
  have hcomm : x * z = z * x :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hxK).2
  have hxz : x * z * x⁻¹ = z := mul_inv_eq_iff_eq_mul.mpr hcomm
  exact mem_normalizer_V_of_conj h.t_sq h.z_sq h.t_mul_z_comm hxz (Rgrp_conj_t h hx)

theorem Rgrp_le_Dgrp (h : Setting25 G t z z₁ ι zv R0 F) : Rgrp h ≤ Dgrp t z R0 := by
  intro x hx
  rw [mem_Dgrp]
  exact ⟨Rgrp_le_normalizer_V h hx, (Subgroup.mem_inf.mp (Rgrp_le_K h hx)).2,
    fun r hr => Rgrp_comm h hx (R0_le_Rgrp h hr)⟩

theorem Dgrp_eq_Rgrp (h : Setting25 G t z z₁ ι zv R0 F) (hzt : ¬ IsConj t z)
    (htz : IsConj t (t * z)) : Dgrp t z R0 = Rgrp h := by
  have hcard : Nat.card (Dgrp t z R0) ≤ Nat.card (Rgrp h) := by
    rw [card_Rgrp h]
    exact card_Dgrp_le h hzt htz
  exact (Subgroup.eq_of_le_of_card_ge (Rgrp_le_Dgrp h) hcard).symm

theorem Rgrp_conj_of_mem_normalizer_V (h : Setting25 G t z z₁ ι zv R0 F) (hzt : ¬ IsConj t z)
    (htz : IsConj t (t * z)) {n x : G}
    (hn : n ∈ normalizer ((zpowers t ⊔ zpowers z : Subgroup G) : Set G)) (hx : x ∈ Rgrp h) :
    n * x * n⁻¹ ∈ Rgrp h := by
  have hxD : x ∈ Dgrp t z R0 := by
    rw [Dgrp_eq_Rgrp h hzt htz]
    exact hx
  have hres := Dgrp_conj h hzt htz hn hxD
  rwa [Dgrp_eq_Rgrp h hzt htz] at hres

end CFSG.EvenSporadicStandard.HNRecog.Harada
