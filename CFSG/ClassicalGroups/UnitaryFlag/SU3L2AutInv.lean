module

public import CFSG.ClassicalGroups.UnitaryFlag.SU3L2Centralizer
public import CFSG.ClassicalGroups.UnitaryFlag.SU3AutLineStabilizer
import CFSG.RankThree.PartTwo.KFacts.AutPSUSylowPoint

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut
  unitarySU_ext_mulVecLin)
open NonisotropicStabilizer Matrix

variable {m : ℕ} {K : Type} [Field K]

theorem suConj_mul_suField_barEquiv_mulVec (h : UnitaryFieldData 2 m K)
    (B : unitaryIsom3 h) (g : unitarySU 2 m K 3) (x : Fin 3 → K) :
    ((((suConj h B * suField h h.barEquiv) g : unitarySU 2 m K 3) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ x =
      ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (((glAut h.barEquiv (g : GL (Fin 3) K) : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) *ᵥ
          ((((B : GL (Fin 3) K)⁻¹) : Matrix (Fin 3) (Fin 3) K) *ᵥ x)) := by
  have hmat : ((((suConj h B * suField h h.barEquiv) g : unitarySU 2 m K 3) :
      GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((glAut h.barEquiv (g : GL (Fin 3) K) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) *
        ((((B : GL (Fin 3) K)⁻¹) : Matrix (Fin 3) (Fin 3) K)) := by
    rw [coe_suConj_mul_suField_apply B h.barEquiv g]
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_inv]
  rw [hmat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem suConj_mul_suField_barEquiv_mulVec_eq_smul (h : UnitaryFieldData 2 m K)
    {v : Fin 3 → K} {B : unitaryIsom3 h} {c : K}
    (hc : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (h.barEquiv ∘ v) = c • v)
    (hc0 : c ≠ 0) {g : unitarySU 2 m K 3} {a : K}
    (hgv : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = a • v) :
    ((((suConj h B * suField h h.barEquiv) g : unitarySU 2 m K 3) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ v = h.barEquiv a • v := by
  have hBinv : ((((B : GL (Fin 3) K)⁻¹) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
      c⁻¹ • (h.barEquiv ∘ v) := by
    simpa [Units.val_inv_eq_inv_val] using
      inv_mulVec_eq_of_mulVec_eq (B : GL (Fin 3) K) (x := c⁻¹ • (h.barEquiv ∘ v))
        (by rw [Matrix.mulVec_smul, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul])
  have hgl : ∀ y : Fin 3 → K,
      ((glAut h.barEquiv (g : GL (Fin 3) K) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ (h.barEquiv ∘ y) =
        h.barEquiv ∘ (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ y) := by
    intro y
    funext i
    rw [coe_glAut, Function.comp_apply]
    exact (RingHom.map_mulVec (h.barEquiv : K →+* K)
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) y i).symm
  have hD : (((glAut h.barEquiv (g : GL (Fin 3) K) : GL (Fin 3) K)) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ (h.barEquiv ∘ v) =
      h.barEquiv a • (h.barEquiv ∘ v) := by
    rw [hgl, hgv]
    funext i
    simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul, map_mul]
  rw [suConj_mul_suField_barEquiv_mulVec, hBinv]
  rw [Matrix.mulVec_smul, hD, Matrix.mulVec_smul, Matrix.mulVec_smul, hc]
  rw [smul_smul, smul_smul]
  congr 1
  field_simp

theorem suConj_mul_suField_barEquiv_mulVec_eq_smul_of_hermPerp
    (h : UnitaryFieldData 2 m K) {v : Fin 3 → K} {B : unitaryIsom3 h} {c : K}
    (hc : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (h.barEquiv ∘ v) = c • v)
    {g : unitarySU 2 m K 3} {b : K}
    (hg : ∀ w : Fin 3 → K, stdHermForm h 3 v w = 0 →
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w = b • w)
    {w : Fin 3 → K} (hw : stdHermForm h 3 v w = 0) :
    ((((suConj h B * suField h h.barEquiv) g : unitarySU 2 m K 3) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ w = h.barEquiv b • w := by
  let y : Fin 3 → K := (((B : GL (Fin 3) K)⁻¹) : Matrix (Fin 3) (Fin 3) K) *ᵥ w
  let x : Fin 3 → K := fun i => h.barEquiv.symm (y i)
  have hδx : h.barEquiv ∘ x = y := by
    funext i
    simp [x]
  have hBy : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ y = w := by
    simpa only [y, Matrix.GeneralLinearGroup.coe_inv] using
      mulVec_conj_inv (B : GL (Fin 3) K) w
  have hδvperp : stdHermForm h 3 (h.barEquiv ∘ v) y = 0 := by
    have hiso := isometry_of_mem_unitaryIsom3 h B (h.barEquiv ∘ v) y
    simp only [Units.smul_def, Matrix.smul_eq_mulVec] at hiso
    rw [hc, hBy] at hiso
    rw [← hiso, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hw, mul_zero]
  have hxperp : stdHermForm h 3 v x = 0 := by
    have hmap : stdHermForm h 3 (h.barEquiv ∘ v) (h.barEquiv ∘ x) =
        h.barEquiv (stdHermForm h 3 v x) := by
      simp only [Function.comp_apply, UnitaryFieldData.barEquiv_apply, stdHermForm_apply,
        map_sum, map_mul, h.bar_bar]
    rw [hδx, hδvperp] at hmap
    exact h.barEquiv.map_eq_zero_iff.mp hmap.symm
  have hgx : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x = b • x := hg x hxperp
  have hgl : ∀ z : Fin 3 → K,
      ((glAut h.barEquiv (g : GL (Fin 3) K) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ (h.barEquiv ∘ z) =
        h.barEquiv ∘ (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ z) := by
    intro z
    funext i
    rw [coe_glAut, Function.comp_apply]
    exact (RingHom.map_mulVec (h.barEquiv : K →+* K)
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) z i).symm
  have hDy : ((glAut h.barEquiv (g : GL (Fin 3) K) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ y = h.barEquiv b • y := by
    rw [← hδx, hgl, hgx]
    funext i
    simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul, map_mul]
  rw [suConj_mul_suField_barEquiv_mulVec,
    show (((B : GL (Fin 3) K)⁻¹) : Matrix (Fin 3) (Fin 3) K) *ᵥ w = y from rfl,
    hDy, Matrix.mulVec_smul, hBy]

theorem eq_of_mulVec_eq_on_nonisotropic_and_hermPerp (h : UnitaryFieldData 2 m K)
    {v : Fin 3 → K} (hv : stdHermForm h 3 v v ≠ 0) {g g' : unitarySU 2 m K 3}
    (hv' : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v =
      ((g' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v)
    (hperp : ∀ w : Fin 3 → K, stdHermForm h 3 v w = 0 →
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w =
        ((g' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) :
    g = g' := by
  obtain ⟨e, f, hee, hff, hef, hev, hfv⟩ := exists_hyperbolic_pair_of_nonisotropic h hv
  have hspan := span_range_hyperbolic_eq_top h hv hee hff hef hev hfv
  apply unitarySU_ext_mulVecLin
  apply LinearMap.ext_on_range hspan
  intro i
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
  fin_cases i
  · simpa using hperp e (((stdHermForm_isSymm h 3).eq_iff).mpr hev)
  · simpa using hperp f (((stdHermForm_isSymm h 3).eq_iff).mpr hfv)
  · simpa using hv'

theorem suConj_mul_suField_barEquiv_apply_eq_inv (h : UnitaryFieldData 2 m K)
    {v : Fin 3 → K} (hv : stdHermForm h 3 v v ≠ 0) {L : Subgroup (unitarySU 2 m K 3)}
    (hL : ∀ g, g ∈ L ↔ ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v)
    {B : unitaryIsom3 h} (hBL : ∀ x ∈ L, (suConj h B * suField h h.barEquiv) x = x)
    {μ : K} (hμ : μ ^ (2 ^ m + 1) = 1) {g : unitarySU 2 m K 3}
    (hgv : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = (μ ^ 2)⁻¹ • v)
    (hgw : ∀ w : Fin 3 → K, stdHermForm h 3 v w = 0 →
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec w = μ • w) :
    (suConj h B * suField h h.barEquiv) g = g⁻¹ := by
  have hv0 : v ≠ 0 := fun h0 => hv (by rw [h0]; simp)
  obtain ⟨c, hc0, hc⟩ := exists_smul_of_suConj_mul_suField_fixes_torus (h := h)
    hv0 (fun b hb => (hL b).mp hb)
    (fun w hw => exists_eq_smul_of_forall_mem_mulVec_eq h hv hL hw)
    (B := B) (δ := h.barEquiv) hBL
  have hnorm : h.norm μ = 1 := by rw [UnitaryFieldData.norm_eq_pow, hμ]
  have hμ0 : μ ≠ 0 := by
    intro h0
    simp [UnitaryFieldData.norm, h0] at hnorm
  have hbarμ : h.bar μ = μ⁻¹ := by
    rw [UnitaryFieldData.bar_apply]
    exact eq_inv_of_mul_eq_one_right (by rwa [pow_succ, mul_comm] at hμ)
  have hbarμ2 : h.barEquiv ((μ ^ 2)⁻¹) = μ ^ 2 := by
    rw [UnitaryFieldData.barEquiv_apply, map_inv₀, map_pow, hbarμ, inv_pow, inv_inv]
  have hαv : ((((suConj h B * suField h h.barEquiv) g : unitarySU 2 m K 3) :
      GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = μ ^ 2 • v := by
    simpa [hbarμ2] using
      suConj_mul_suField_barEquiv_mulVec_eq_smul h hc hc0 hgv
  have hαw : ∀ w : Fin 3 → K, stdHermForm h 3 v w = 0 →
      ((((suConj h B * suField h h.barEquiv) g : unitarySU 2 m K 3) :
        GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w = μ⁻¹ • w := by
    intro w hw
    simpa [UnitaryFieldData.barEquiv_apply, hbarμ] using
      suConj_mul_suField_barEquiv_mulVec_eq_smul_of_hermPerp h hc hgw hw
  have hgInv_v : (((g⁻¹ : unitarySU 2 m K 3) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ v = μ ^ 2 • v := by
    rw [Subgroup.coe_inv]
    refine inv_mulVec_eq_of_mulVec_eq (g : GL (Fin 3) K) ?_
    rw [Matrix.mulVec_smul, hgv, smul_smul,
      mul_inv_cancel₀ (pow_ne_zero 2 hμ0), one_smul]
  have hgInv_w : ∀ w : Fin 3 → K, stdHermForm h 3 v w = 0 →
      (((g⁻¹ : unitarySU 2 m K 3) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ w = μ⁻¹ • w := by
    intro w hw
    rw [Subgroup.coe_inv]
    refine inv_mulVec_eq_of_mulVec_eq (g : GL (Fin 3) K) ?_
    rw [Matrix.mulVec_smul, hgw w hw, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
  exact eq_of_mulVec_eq_on_nonisotropic_and_hermPerp h hv
    (by rw [hαv, hgInv_v])
    (fun w hw => by rw [hαw w hw, hgInv_w w hw])

end CFSG.ClassicalGroups.UnitaryFlag

end
