module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.GDefs
public import CFSG.Sporadic.Co1Patterson.SettingOmega
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Extraspecial.PlusType
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NVD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA CFSG.EvenSporadicStandard.HNRecog
  CFSG.RankThree.Literature.FSmith

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G}

theorem ker_rho0 (h : Setting25 G t z z₁ ι zv R0 F) : (rho0 h).ker = Qsub h :=
  ker_extraspecialConjOrth (isPlusExtraspecial_Qsub h).isExtraspecialPGroup
    (centralizer_Qsub_le h)

theorem rho0_toW (h : Setting25 G t z z₁ ι zv R0 F) (g : ↥(Ngrp h)) {x : G} (hx : x ∈ Rgrp h) :
    ((rho0 h g : TauCeti.QuadraticMap.orthogonalGroup (qW h)) : Wsp h ≃ₗ[ZMod 2] Wsp h)
        (toW h x hx) =
      toW h ((g : G) * x * (g : G)⁻¹) (conj_mem_Rgrp h g.2 hx) := by
  have h1 := extraspecialConjOrth_apply (isPlusExtraspecial_Qsub h).isExtraspecialPGroup
    (inferInstance : (Qsub h).Normal) g
    (⟨⟨x, Rgrp_le_Ngrp h hx⟩, Subgroup.mem_subgroupOf.2 hx⟩ : Qsub h)
  refine h1.trans ?_
  unfold toW
  congr 2

theorem toW_mul (h : Setting25 G t z z₁ ι zv R0 F) {x y : G} (hx : x ∈ Rgrp h)
    (hy : y ∈ Rgrp h) : toW h (x * y) (mul_mem hx hy) = toW h x hx + toW h y hy := by
  unfold toW
  rw [← ofMul_of_mul]
  rfl

theorem toW_eq_zero_iff (h : Setting25 G t z z₁ ι zv R0 F) {x : G} (hx : x ∈ Rgrp h) :
    toW h x hx = 0 ↔ x ∈ zpowers z := by
  unfold toW
  rw [ofMul_of_eq_zero_iff (isPlusExtraspecial_Qsub h).isExtraspecialPGroup,
    Subgroup.mem_center_iff]
  constructor
  · intro hc
    refine Rgrp_center_le h hx fun y hy => ?_
    have := hc ⟨⟨y, Rgrp_le_Ngrp h hy⟩, Subgroup.mem_subgroupOf.2 hy⟩
    exact (congrArg (fun q : Qsub h => (((q : ↥(Ngrp h)) : G))) this).symm
  · intro hz r
    have hzc : ∀ y ∈ Rgrp h, y * z = z * y := fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (Rgrp_le_K h hy)).2
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact Subtype.ext (Subtype.ext (((Commute.zpow_right
      (show Commute (((r : ↥(Ngrp h)) : G)) z from hzc _ (Subgroup.mem_subgroupOf.mp r.2)) k)).eq))

theorem toW_inv (h : Setting25 G t z z₁ ι zv R0 F) {x : G} (hx : x ∈ Rgrp h) :
    toW h x⁻¹ (inv_mem hx) = toW h x hx := by
  have h1 : toW h x⁻¹ (inv_mem hx) + toW h x hx = 0 := by
    rw [← toW_mul h (inv_mem hx) hx]
    exact (toW_eq_zero_iff h (mul_mem (inv_mem hx) hx)).2 (by simp [one_mem])
  have h2 : toW h x hx + toW h x hx = 0 := by
    rw [← toW_mul h hx hx]
    exact (toW_eq_zero_iff h (mul_mem hx hx)).2 (by simpa [pow_two] using Rgrp_sq h hx)
  have h3 : toW h x⁻¹ (inv_mem hx) = - toW h x hx := eq_neg_of_add_eq_zero_left h1
  have h4 : toW h x hx = - toW h x hx := eq_neg_of_add_eq_zero_left h2
  rw [h3, ← h4]

theorem toW_eq_toW_iff (h : Setting25 G t z z₁ ι zv R0 F) {x y : G} (hx : x ∈ Rgrp h)
    (hy : y ∈ Rgrp h) : toW h x hx = toW h y hy ↔ x * y⁻¹ ∈ zpowers z := by
  rw [← toW_eq_zero_iff h (mul_mem hx (inv_mem hy)), toW_mul h hx (inv_mem hy), toW_inv h hy]
  constructor
  · intro hxy
    rw [hxy]
    have h2 : toW h y hy + toW h y hy = 0 := by
      rw [← toW_mul h hy hy]
      exact (toW_eq_zero_iff h (mul_mem hy hy)).2 (by simpa [pow_two] using Rgrp_sq h hy)
    exact h2
  · intro h0
    exact (eq_neg_of_add_eq_zero_left h0).trans (by
      have h2 : toW h y hy + toW h y hy = 0 := by
        rw [← toW_mul h hy hy]
        exact (toW_eq_zero_iff h (mul_mem hy hy)).2 (by simpa [pow_two] using Rgrp_sq h hy)
      exact (eq_neg_of_add_eq_zero_left h2).symm)

theorem toW_surjective (h : Setting25 G t z z₁ ι zv R0 F) (w : Wsp h) :
    ∃ (x : G) (hx : x ∈ Rgrp h), toW h x hx = w := by
  obtain ⟨q, rfl⟩ := exists_ofMul_of w
  exact ⟨((q : ↥(Ngrp h)) : G), Subgroup.mem_subgroupOf.mp q.2, rfl⟩

theorem qW_toW (h : Setting25 G t z z₁ ι zv R0 F) {x : G} (hx : x ∈ Rgrp h) :
    qW h (toW h x hx) = 0 ↔ x ^ 2 = 1 := by
  unfold qW toW
  rw [extraspecialQuadForm_apply]
  by_cases hx2 : x ^ 2 = 1
  · have : (⟨⟨x, Rgrp_le_Ngrp h hx⟩, Subgroup.mem_subgroupOf.2 hx⟩ : Qsub h) ^ 2 = 1 :=
      Subtype.ext (Subtype.ext (by simpa using hx2))
    simp [this, hx2]
  · have : ¬ (⟨⟨x, Rgrp_le_Ngrp h hx⟩, Subgroup.mem_subgroupOf.2 hx⟩ : Qsub h) ^ 2 = 1 :=
      fun hh => hx2 (by simpa using congrArg (fun q : Qsub h => (((q : ↥(Ngrp h)) : G))) hh)
    simp [this, hx2]

theorem polar_toW (h : Setting25 G t z z₁ ι zv R0 F) {x y : G} (hx : x ∈ Rgrp h)
    (hy : y ∈ Rgrp h) :
    QuadraticMap.polar (qW h) (toW h x hx) (toW h y hy) = 0 ↔ x * y = y * x := by
  unfold qW toW
  rw [polar_extraspecialQuadForm_eq_zero_iff]
  constructor
  · intro hh
    exact congrArg (fun q : Qsub h => (((q : ↥(Ngrp h)) : G))) hh
  · intro hh
    exact Subtype.ext (Subtype.ext hh)

theorem nondegenerate_qW (h : Setting25 G t z z₁ ι zv R0 F) :
    (qW h).polarBilin.Nondegenerate :=
  extraspecialQuadForm_nondegenerate _

theorem rhoX_polar (h : Setting25 G t z z₁ ι zv R0 F) (g : ↥(Xgrp h)) (x y : Wsp h) :
    (qW h).polarBilin ((rhoX h g : Wsp h ≃ₗ[ZMod 2] Wsp h) x)
        ((rhoX h g : Wsp h ≃ₗ[ZMod 2] Wsp h) y) = (qW h).polarBilin x y := by
  have hq : ∀ v : Wsp h, qW h ((rhoX h g : Wsp h ≃ₗ[ZMod 2] Wsp h) v) = qW h v := fun v =>
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup g.1.2 v
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, hq]

theorem finrank_Wsp (h : Setting25 G t z z₁ ι zv R0 F) :
    Module.finrank (ZMod 2) (Wsp h) = 8 :=
  (isPlusExtraspecial_Qsub h).finrank_quotient

theorem card_Xgrp_dvd (h : Setting25 G t z z₁ ι zv R0 F) : Nat.card (Xgrp h) ∣ 348364800 := by
  have hplus := (isPlusExtraspecial_Qsub h).isPlusType_extraspecialQuadForm
  rcases CFSG.Sporadic.Co1Patterson.natCard_orthogonalGroup_of_finrank_eight
    (nondegenerate_qW h) (finrank_Wsp h) with ⟨-, hc⟩ | ⟨hn, -⟩
  · exact hc ▸ Subgroup.card_subgroup_dvd_card (Xgrp h)
  · exact absurd hplus hn

theorem qW_wvec (h : Setting25 G t z z₁ ι zv R0 F) : qW h (wvec h) = 0 :=
  (qW_toW h (Setting25.t_mem_Rgrp h)).2 h.t_sq

theorem wvec_ne_zero (h : Setting25 G t z z₁ ι zv R0 F) (hzt : ¬ IsConj t z)
    (htz : IsConj t (t * z)) : wvec h ≠ 0 := by
  intro h0
  have hmem : t ∈ zpowers z := (toW_eq_zero_iff h (Setting25.t_mem_Rgrp h)).1 h0
  have hord : orderOf z = 2 := orderOf_eq_prime h.z_sq h.z_ne_one
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rw [← zpow_mod_orderOf z k, hord] at hk
  norm_num only [Nat.cast_ofNat] at hk
  rcases Int.emod_two_eq_zero_or_one k with hk2 | hk2
  · rw [hk2] at hk
    have ht1 : t = 1 := by simpa using hk.symm
    rw [ht1, one_mul] at htz
    exact h.z_ne_one (isConj_one_left.mp (by simpa using htz.symm))
  · rw [hk2] at hk
    have hzt' : z = t := by simpa using hk
    exact hzt (by rw [← hzt'])

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
