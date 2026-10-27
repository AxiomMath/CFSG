module

public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceSpZ

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MFO.Sp

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped Matrix MatrixGroups

section Matrix

variable {F : Type} [Field F]

theorem multiplier_eq_sq_of_commute (A B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (μ : F)
    (hBA : B * A = 1)
    (hU : A * Matrix.single (Sum.inl 0) (Sum.inr 0) (1 : F) =
      Matrix.single (Sum.inl 0) (Sum.inr 0) 1 * A)
    (hL : A * Matrix.single (Sum.inr 0) (Sum.inl 0) (1 : F) =
      Matrix.single (Sum.inr 0) (Sum.inl 0) 1 * A)
    (hA : Aᵀ * gram F 2 * A = μ • gram F 2) :
    ∃ l : F, l ≠ 0 ∧ μ = l * l := by
  have hl : ∀ r : Fin 2 ⊕ Fin 2, r ≠ Sum.inl 0 → A r (Sum.inl 0) = 0 := by
    intro r hr
    have := congrFun (congrFun hU r) (Sum.inr 0)
    rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne (h := hr)] at this
    simpa using this
  have hr' : ∀ r : Fin 2 ⊕ Fin 2, r ≠ Sum.inr 0 → A r (Sum.inr 0) = 0 := by
    intro r hr
    have := congrFun (congrFun hL r) (Sum.inl 0)
    rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne (h := hr)] at this
    simpa using this
  have hd : A (Sum.inl 0) (Sum.inl 0) = A (Sum.inr 0) (Sum.inr 0) := by
    have := congrFun (congrFun hU (Sum.inl 0)) (Sum.inr 0)
    rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_same] at this
    simpa using this
  refine ⟨A (Sum.inl 0) (Sum.inl 0), ?_, ?_⟩
  · intro h0
    have := congrFun (congrFun hBA (Sum.inl 0)) (Sum.inl 0)
    rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inl 0)] at this
    · rw [h0, mul_zero] at this
      simp at this
    · intro t _ ht
      rw [hl t ht, mul_zero]
    · simp
  · have := congrFun (congrFun hA (Sum.inl 0)) (Sum.inr 0)
    rw [transpose_mul_gram_mul_apply, Finset.sum_eq_single (Sum.inl 0)] at this
    · simpa [gram_apply, sgn, par, hd] using this.symm
    · intro b _ hb
      rw [hl b hb, zero_mul]
    · simp

end Matrix

section Group

open CFSG.ClassicalInvolution.Balance.StrongBalance.Sp
  (simMat simInv simInv_mul simMat_mul mat_conjSp mat_longBlock_upper mat_longBlock_lower negOne
  mat_negOne negOne_mul_self negOne_ne_one mem_center_iff)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

variable {F : Type} [Field F] [Finite F]

theorem conjSp_eq_of_conjAut_eq (h2 : (2 : F) ≠ 0) (A : gsp 2 F) {s : StatedSp 2 F}
    (hs : s ^ 3 = 1) (h : conjAut 2 F A (proj 2 F s) = proj 2 F s) : conjSp 2 F A s = s := by
  rw [conjAut_proj] at h
  have h1 : (conjSp 2 F A s)⁻¹ * s ∈ spScalars 2 F := QuotientGroup.eq.mp h
  have hz : (conjSp 2 F A s)⁻¹ * s ∈ Subgroup.center (StatedSp 2 F) := by
    rw [CFSG.LieType.Universal.Symplectic.center_eq 2 F]
    exact h1
  rcases mem_center_iff.mp hz with h0 | h0
  · exact inv_mul_eq_one.mp h0
  · exfalso
    have e : s = conjSp 2 F A s * negOne := by
      calc s = conjSp 2 F A s * ((conjSp 2 F A s)⁻¹ * s) := by group
        _ = conjSp 2 F A s * negOne := by rw [h0]
    have hcen : (negOne : StatedSp 2 F) ∈ Subgroup.center (StatedSp 2 F) :=
      mem_center_iff.mpr (Or.inr rfl)
    have hc : Commute (conjSp 2 F A s) negOne :=
      (Subgroup.mem_center_iff.mp hcen (conjSp 2 F A s))
    have h3 : s ^ 3 = (conjSp 2 F A s) ^ 3 * negOne ^ 3 := by
      conv_lhs => rw [e]
      exact hc.mul_pow 3
    have hn3 : (negOne : StatedSp 2 F) ^ 3 = negOne := by
      rw [pow_succ, pow_two, negOne_mul_self, one_mul]
    rw [hs, ← map_pow, hs, map_one, one_mul, hn3] at h3
    exact negOne_ne_one h2 h3.symm

theorem mul_eq_of_conjSp_eq' (A : gsp 2 F) {s : StatedSp 2 F} (h : conjSp 2 F A s = s) :
    simMat A * mat 2 F s = mat 2 F s * simMat A := by
  have h1 := congrArg (mat 2 F) h
  rw [mat_conjSp] at h1
  calc simMat A * mat 2 F s = simMat A * mat 2 F s * (simInv A * simMat A) := by
        rw [simInv_mul, mul_one]
    _ = (simMat A * mat 2 F s * simInv A) * simMat A := by simp only [Matrix.mul_assoc]
    _ = mat 2 F s * simMat A := by rw [h1]

noncomputable abbrev tU (F : Type) [Field F] : StatedSp 2 F := longBlock F 2 0 (sl2Upper (1 : F))

noncomputable abbrev tL (F : Type) [Field F] : StatedSp 2 F := longBlock F 2 0 (sl2Lower (1 : F))

theorem mat_tU : mat 2 F (tU F) = 1 + Matrix.single (Sum.inl 0) (Sum.inr 0) (1 : F) := by
  rw [mat_longBlock_upper]
  rfl

theorem mat_tL : mat 2 F (tL F) = 1 + Matrix.single (Sum.inr 0) (Sum.inl 0) (1 : F) := by
  rw [mat_longBlock_lower]
  rfl

theorem tU_pow_three (h3 : (3 : F) = 0) : (tU F) ^ 3 = 1 := by
  refine mat_injective ?_
  have hne : (Sum.inl 0 : Fin 2 ⊕ Fin 2) ≠ Sum.inr 0 := Sum.inl_ne_inr
  rw [map_pow, map_one, mat_longBlock_upper, pow_succ, pow_succ, pow_one,
    Matrix.transvection_mul_transvection_same _ _ hne (1 : F) 1,
    Matrix.transvection_mul_transvection_same _ _ hne (1 + 1 : F) 1]
  have : (1 : F) + 1 + 1 = 0 := by rw [← h3]; norm_num
  rw [this, Matrix.transvection_zero]

theorem tL_pow_three (h3 : (3 : F) = 0) : (tL F) ^ 3 = 1 := by
  refine mat_injective ?_
  have hne : (Sum.inr 0 : Fin 2 ⊕ Fin 2) ≠ Sum.inl 0 := Sum.inr_ne_inl
  rw [map_pow, map_one, mat_longBlock_lower, pow_succ, pow_succ, pow_one,
    Matrix.transvection_mul_transvection_same _ _ hne (1 : F) 1,
    Matrix.transvection_mul_transvection_same _ _ hne (1 + 1 : F) 1]
  have : (1 : F) + 1 + 1 = 0 := by rw [← h3]; norm_num
  rw [this, Matrix.transvection_zero]

end Group

section Plane

open CFSG.LocalAnalysis.ComponentInitial (pairedSympForm pairedSympForm_apply)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (IsTotallyIsotropic)

variable {F : Type} [Field F]

theorem mulVec_tU (w : Fin 2 ⊕ Fin 2 → F) :
    (1 + Matrix.single (Sum.inl 0) (Sum.inr 0) (1 : F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w =
      w + w (Sum.inr 0) • (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → F) := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq, one_mul]

theorem mulVec_tL (w : Fin 2 ⊕ Fin 2 → F) :
    (1 + Matrix.single (Sum.inr 0) (Sum.inl 0) (1 : F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w =
      w + w (Sum.inl 0) • (Pi.single (Sum.inr 0) 1 : Fin 2 ⊕ Fin 2 → F) := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq, one_mul]

theorem form_ex_ey :
    pairedSympForm F 2 (Pi.single (Sum.inl 0) 1) (Pi.single (Sum.inr 0) 1) = 1 := by
  rw [pairedSympForm_apply]
  simp [dotProduct, Pi.single_apply]

theorem not_both_mem_of_isotropic {W : Submodule F (Fin 2 ⊕ Fin 2 → F)}
    (hiso : IsTotallyIsotropic (pairedSympForm F 2) W)
    (h1 : (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → F) ∈ W)
    (h2 : (Pi.single (Sum.inr 0) 1 : Fin 2 ⊕ Fin 2 → F) ∈ W) : False := by
  have := hiso _ h1 _ h2
  rw [form_ex_ey] at this
  exact one_ne_zero this

theorem single_inl_mem_of_ne {W : Submodule F (Fin 2 ⊕ Fin 2 → F)}
    (hU : ∀ w ∈ W, (1 + Matrix.single (Sum.inl 0) (Sum.inr 0) (1 : F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w ∈ W)
    {w : Fin 2 ⊕ Fin 2 → F} (hw : w ∈ W) (hw0 : w (Sum.inr 0) ≠ 0) :
    (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → F) ∈ W := by
  have h1 := W.sub_mem (hU w hw) hw
  rw [mulVec_tU, add_sub_cancel_left] at h1
  have := W.smul_mem (w (Sum.inr 0))⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hw0, one_smul] at this

theorem single_inr_mem_of_ne {W : Submodule F (Fin 2 ⊕ Fin 2 → F)}
    (hL : ∀ w ∈ W, (1 + Matrix.single (Sum.inr 0) (Sum.inl 0) (1 : F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w ∈ W)
    {w : Fin 2 ⊕ Fin 2 → F} (hw : w ∈ W) (hw0 : w (Sum.inl 0) ≠ 0) :
    (Pi.single (Sum.inr 0) 1 : Fin 2 ⊕ Fin 2 → F) ∈ W := by
  have h1 := W.sub_mem (hL w hw) hw
  rw [mulVec_tL, add_sub_cancel_left] at h1
  have := W.smul_mem (w (Sum.inl 0))⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hw0, one_smul] at this

theorem no_invariant_isotropic_plane (W : Submodule F (Fin 2 ⊕ Fin 2 → F))
    (hiso : IsTotallyIsotropic (pairedSympForm F 2) W) (hdim : Module.finrank F W = 2)
    (hU : ∀ w ∈ W, (1 + Matrix.single (Sum.inl 0) (Sum.inr 0) (1 : F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w ∈ W)
    (hL : ∀ w ∈ W, (1 + Matrix.single (Sum.inr 0) (Sum.inl 0) (1 : F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w ∈ W) : False := by
  by_cases hA : ∃ w ∈ W, w (Sum.inr 0) ≠ 0
  · obtain ⟨w, hw, hw0⟩ := hA
    have hx := single_inl_mem_of_ne hU hw hw0
    have hy := single_inr_mem_of_ne hL hx (by simp)
    exact not_both_mem_of_isotropic hiso hx hy
  by_cases hB : ∃ w ∈ W, w (Sum.inl 0) ≠ 0
  · obtain ⟨w, hw, hw0⟩ := hB
    have hy := single_inr_mem_of_ne hL hw hw0
    have hx := single_inl_mem_of_ne hU hy (by simp)
    exact not_both_mem_of_isotropic hiso hx hy
  push Not at hA hB
  let φ : W →ₗ[F] (Fin 2 → F) :=
    { toFun := fun w => ![w.1 (Sum.inl 1), w.1 (Sum.inr 1)]
      map_add' := fun x y => by ext i; fin_cases i <;> simp
      map_smul' := fun c x => by ext i; fin_cases i <;> simp }
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have h0 := congrFun hw 0
    have h1 := congrFun hw 1
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.zero_apply] at h0 h1
    refine Subtype.ext (funext fun t => ?_)
    rcases t with t | t <;> fin_cases t
    · exact hB w.1 w.2
    · exact h0
    · exact hA w.1 w.2
    · exact h1
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [hdim, Module.finrank_fin_fun])).mp hinj
  obtain ⟨u, hu⟩ := hsurj ![1, 0]
  obtain ⟨v, hv⟩ := hsurj ![0, 1]
  have hu0 := congrFun hu 0
  have hu1 := congrFun hu 1
  have hv0 := congrFun hv 0
  have hv1 := congrFun hv 1
  simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
    at hu0 hu1 hv0 hv1
  have h := hiso _ u.2 _ v.2
  rw [pairedSympForm_apply] at h
  simp [dotProduct, Fin.sum_univ_two, hA _ u.2, hA _ v.2, hB _ u.2, hB _ v.2, hu0, hu1, hv0,
    hv1] at h

end Plane

end CFSG.ClassicalInvolution.Q3.Q3MFO.Sp
