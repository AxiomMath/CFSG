module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityOrthSymmetry

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer (mem_matrixDerived_iff)

variable {K : Type} [Field K] {d : ℕ}

section Quotient

variable (Q : QuadraticForm K (Fin d → K)) (v : Fin d → K)

abbrev vPerp : Submodule K (Fin d → K) := LinearMap.ker (Q.polarBilin v)

theorem mem_vPerp {x : Fin d → K} : x ∈ vPerp Q v ↔ polar Q v x = 0 := Iff.rfl

abbrev vLine : Submodule K (vPerp Q v) := (K ∙ v).comap (vPerp Q v).subtype

abbrev perpForm : LinearMap.BilinForm K (vPerp Q v) :=
  LinearMap.BilinForm.restrict Q.polarBilin (vPerp Q v)

theorem perpForm_apply (x y : vPerp Q v) : perpForm Q v x y = polar Q x y := rfl

theorem perpForm_isRefl : (perpForm Q v).IsRefl := fun x y h => by
  rw [perpForm_apply] at h ⊢
  rw [polar_comm, h]

theorem vLine_le_ker : vLine Q v ≤ LinearMap.ker (perpForm Q v) := by
  intro x hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
  have hc' : (x : Fin d → K) = c • v := hc.symm
  rw [LinearMap.mem_ker]
  refine LinearMap.ext fun y => ?_
  rw [perpForm_apply, LinearMap.zero_apply, hc', polar_smul_left, smul_eq_mul,
    (mem_vPerp Q v).mp y.2, mul_zero]

abbrev vQuot : Type := vPerp Q v ⧸ vLine Q v

@[expose] def vQuotForm : LinearMap.BilinForm K (vQuot Q v) :=
  LinearMap.IsRefl.liftQ₂ (perpForm Q v) (vLine Q v) (perpForm_isRefl Q v) (vLine_le_ker Q v)

theorem vQuotForm_mk (x y : vPerp Q v) :
    vQuotForm Q v (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = polar Q x y := rfl

theorem vQuotForm_isAlt [CharP K 2] : (vQuotForm Q v).IsAlt := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    rw [vQuotForm_mk, polar_self, two_nsmul, CharTwo.add_self_eq_zero]

variable {Q v}

theorem exists_polar_eq_one (hQ : Q.polarBilin.Nondegenerate) (hv0 : v ≠ 0) :
    ∃ w, polar Q v w = 1 := by
  obtain ⟨y, hy⟩ : ∃ y, polar Q v y ≠ 0 := by
    by_contra! h0
    exact hv0 (hQ.1 v fun y => by rw [QuadraticMap.polarBilin_apply_apply]; exact h0 y)
  exact ⟨(polar Q v y)⁻¹ • y, by rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hy]⟩

theorem sub_smul_mem_vPerp {w : Fin d → K} (hw : polar Q v w = 1) (x : Fin d → K) :
    x - polar Q v x • w ∈ vPerp Q v := by
  rw [mem_vPerp, polar_sub_right, polar_smul_right, hw, smul_eq_mul, mul_one, sub_self]

theorem mem_vLine_of_forall (hQ : Q.polarBilin.Nondegenerate) (hv0 : v ≠ 0) {x : vPerp Q v}
    (hx : ∀ y : vPerp Q v, polar Q x y = 0) : x ∈ vLine Q v := by
  obtain ⟨w, hw⟩ := exists_polar_eq_one hQ hv0
  set c := polar Q x w with hc
  have hz : ∀ u, polar Q ((x : Fin d → K) - c • v) u = 0 := by
    intro u
    have h1 := hx ⟨_, sub_smul_mem_vPerp hw u⟩
    simp only [polar_sub_left, polar_sub_right, polar_smul_left, polar_smul_right,
      smul_eq_mul] at h1 ⊢
    rw [← hc] at h1
    linear_combination h1
  have hz0 := hQ.1 _ fun u => by rw [QuadraticMap.polarBilin_apply_apply]; exact hz u
  rw [sub_eq_zero] at hz0
  exact Submodule.mem_span_singleton.mpr ⟨c, hz0.symm⟩

theorem vQuotForm_nondegenerate (hQ : Q.polarBilin.Nondegenerate) (hv0 : v ≠ 0) :
    (vQuotForm Q v).Nondegenerate := by
  have key : ∀ x : vQuot Q v, (∀ y : vQuot Q v, vQuotForm Q v x y = 0) → x = 0 := by
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [Submodule.Quotient.mk_eq_zero]
      exact mem_vLine_of_forall hQ hv0 fun y => hx (Submodule.Quotient.mk y)
  refine ⟨key, fun y hy => key y fun x => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      rw [vQuotForm_mk, polar_comm, ← vQuotForm_mk]
      exact hy _

theorem finrank_vQuot [CharP K 2] (hQ : Q.polarBilin.Nondegenerate) (hv : Q v = 1) :
    Module.finrank K (vQuot Q v) + 2 = d := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  obtain ⟨w, hw⟩ := exists_polar_eq_one hQ hv0
  have h1 := LinearMap.finrank_range_add_finrank_ker (Q.polarBilin v)
  have hrange : LinearMap.range (Q.polarBilin v) = ⊤ := by
    rw [eq_top_iff]
    intro c _
    refine ⟨c • w, ?_⟩
    rw [map_smul, QuadraticMap.polarBilin_apply_apply, hw, smul_eq_mul, mul_one]
  rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h1
  change 1 + Module.finrank K (vPerp Q v) = d at h1
  have hvp : (K ∙ v) ≤ vPerp Q v := by
    rw [Submodule.span_singleton_le_iff_mem, mem_vPerp, polar_self, hv, two_nsmul,
      CharTwo.add_self_eq_zero]
  have h2 : Module.finrank K (vLine Q v) = 1 := by
    rw [LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hvp), finrank_span_singleton hv0]
  have h3 := Submodule.finrank_quotient_add_finrank (vLine Q v)
  rw [h2] at h3
  change Module.finrank K (vQuot Q v) + 1 = Module.finrank K (vPerp Q v) at h3
  omega

end Quotient

section Fix

variable {Q : QuadraticForm K (Fin d → K)} {v : Fin d → K}
  {e : (Fin d → K) ≃ₗ[K] (Fin d → K)} (hev : e v = v)
  (hep : ∀ x y, polar Q (e x) (e y) = polar Q x y)
include hev hep

theorem map_vPerp_of_fix : (vPerp Q v).map (e : (Fin d → K) →ₗ[K] (Fin d → K)) = vPerp Q v := by
  ext x
  simp only [Submodule.mem_map, LinearEquiv.coe_coe, mem_vPerp]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← hev, hep, hy]
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    rw [← hep, hev, e.apply_symm_apply, hx]

@[expose] def perpEquivOfFix : vPerp Q v ≃ₗ[K] vPerp Q v :=
  e.ofSubmodules _ _ (map_vPerp_of_fix hev hep)

theorem coe_perpEquivOfFix (x : vPerp Q v) :
    (perpEquivOfFix hev hep x : Fin d → K) = e x := rfl

theorem map_vLine_of_fix :
    (vLine Q v).map (perpEquivOfFix hev hep : vPerp Q v →ₗ[K] vPerp Q v) = vLine Q v := by
  ext x
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply,
    LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy
    rw [coe_perpEquivOfFix, ← hc, map_smul, hev]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v)
  · intro hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
    refine ⟨(perpEquivOfFix hev hep).symm x, ?_, (perpEquivOfFix hev hep).apply_symm_apply x⟩
    have h1 : e (((perpEquivOfFix hev hep).symm x : vPerp Q v) : Fin d → K) = x := by
      rw [← coe_perpEquivOfFix hev hep, LinearEquiv.apply_symm_apply]
    have h2 : (((perpEquivOfFix hev hep).symm x : vPerp Q v) : Fin d → K) = c • v := by
      apply e.injective
      rw [h1, map_smul, hev, hc]
    rw [h2]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v)

@[expose] def quotEquivOfFix : vQuot Q v ≃ₗ[K] vQuot Q v :=
  Submodule.Quotient.equiv _ _ (perpEquivOfFix hev hep) (map_vLine_of_fix hev hep)

theorem quotEquivOfFix_mk (x : vPerp Q v) :
    quotEquivOfFix hev hep (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (perpEquivOfFix hev hep x) := rfl

end Fix

end CFSG.ComponentClassification.UnbalancedCatalog
