module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIsotropicRadical

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag

variable {f n : ℕ} {K : Type} [Field K]

theorem eq_one_of_pow_four_eq_one_of_charTwo [CharP K 2] {x : K} (hx : x ^ 4 = 1) : x = 1 := by
  have h2 : ∀ y : K, y * y = 1 → y = 1 := fun y hy => by
    rcases mul_self_eq_one_iff.mp hy with h | h
    · exact h
    · rw [h, CharTwo.neg_eq]
  refine h2 x (h2 (x * x) ?_)
  rw [← hx]
  ring

theorem ringEquiv_eq_refl_or_bar_of_fixes (h : UnitaryFieldData 2 f K) {φ : K ≃+* K}
    (hφ : ∀ a ∈ h.fixedField, φ a = a) : φ = RingEquiv.refl K ∨ ∀ c, φ c = h.bar c := by
  have hroot : ∀ c, φ c = c ∨ φ c = h.bar c := by
    intro c
    have htr : φ (c + h.bar c) = c + h.bar c := hφ _ (h.trace_mem_fixedField c)
    have hnm : φ (c * h.bar c) = c * h.bar c := hφ _ (h.norm_mem_fixedField c)
    have h1 : (φ c - c) * (φ c - h.bar c) = 0 := by
      have h3 : φ (c * c - (c + h.bar c) * c + c * h.bar c) = 0 := by
        rw [show c * c - (c + h.bar c) * c + c * h.bar c = 0 by ring, map_zero]
      rw [map_add, map_sub, map_mul, map_mul, htr, hnm] at h3
      linear_combination h3
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact Or.inl (sub_eq_zero.mp h2)
    · exact Or.inr (sub_eq_zero.mp h2)
  refine ringEquiv_eq_refl_or_bar h (RingEquiv.ext fun c => ?_)
  change φ (φ c) = c
  rcases hroot c with h1 | h1
  · rw [h1, h1]
  · rw [h1]
    rcases hroot (h.bar c) with h2 | h2
    · have h3 : c = h.bar c := φ.injective (h1.trans h2.symm)
      rw [h2, ← h3]
    · rw [h2, h.bar_bar]

theorem scalar_fin_mulVec (c : K) (v : Fin n → K) : Matrix.scalar (Fin n) c *ᵥ v = c • v := by
  funext i
  simp [scalar_apply, mulVec_diagonal]

section Centralizer

variable (h : UnitaryFieldData 2 f K) {C : GL (Fin n) K} (hC : IsPrimeFormGram C)
  {W : Submodule K (Fin n → K)}
  (hWiso : ∀ v ∈ W, ∀ w ∈ W, gramForm h (C : Matrix (Fin n) (Fin n) K) v w = 0)

theorem isRadicalMatrix_sub_one_pow_three {M : Matrix (Fin n) (Fin n) K}
    (hM : IsRadicalMatrix h (C : Matrix (Fin n) (Fin n) K) W M) : (M - 1) ^ 3 = 0 := by
  obtain ⟨h1, h2, h3⟩ := hM
  refine sub_one_pow_three_eq_zero fun v => ?_
  rw [h1 _ (h2 _ (h3 v)), sub_self]

theorem exists_gramForm_ne_zero {w : Fin n → K} (hw : w ≠ 0) :
    ∃ x, gramForm h (C : Matrix (Fin n) (Fin n) K) w x ≠ 0 := by
  by_contra hall
  push Not at hall
  exact hw (gramForm_separatingLeft h (primeFormGram_det_ne_zero C) w hall)

include hC hWiso in
theorem transvection_mem_radical [CharP K 2] {w : Fin n → K} (hw : w ∈ W) {a : K}
    (ha : a ∈ h.fixedField) :
    ∃ t : gramSU h (C : Matrix (Fin n) (Fin n) K), t ∈ isotropicRadical h _ W ∧
      ∀ v, ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v =
        v + (a * gramForm h (C : Matrix (Fin n) (Fin n) K) w v) • w := by
  have hH := gramForm_isSymm h (hC.barTranspose h)
  have h00 : gramForm h (C : Matrix (Fin n) (Fin n) K) 0 0 = 0 := by simp
  have hc : a + h.bar a = -gramForm h (C : Matrix (Fin n) (Fin n) K) 0 0 := by
    rw [h.mem_fixedField.mp ha, h00, neg_zero, ← two_mul, CharTwo.two_eq_zero, zero_mul]
  refine ⟨_, eichler_mem_radical hH hWiso hw (zero_mem _) hc, fun v => ?_⟩
  change eichlerMatrix h _ w 0 a *ᵥ v = _
  rw [eichlerMatrix_mulVec]
  simp

include hC hWiso in
theorem exists_scalar_mul_mem_radical [CharP K 2] (hW0 : W ≠ ⊥) {A : GL (Fin n) K}
    (hA : A ∈ primeFormUnitary h (C : Matrix (Fin n) (Fin n) K))
    (hcomm : ∀ g ∈ isotropicRadical h (C : Matrix (Fin n) (Fin n) K) W,
      A * ((g : gramSU h _) : GL (Fin n) K) = (g : GL (Fin n) K) * A) :
    ∃ μ : Kˣ, h.norm (μ : K) = 1 ∧ ∃ z : gramSU h (C : Matrix (Fin n) (Fin n) K),
      z ∈ isotropicRadical h _ W ∧
        (z : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) μ⁻¹ * A := by
  set Hf := gramForm h (C : Matrix (Fin n) (Fin n) K) with hHf
  set Am := (A : Matrix (Fin n) (Fin n) K) with hAm
  have hH : Hf.IsSymm := gramForm_isSymm h (hC.barTranspose h)
  have hAiso : ∀ x y, Hf (Am *ᵥ x) (Am *ᵥ y) = Hf x y :=
    (gramForm_isometry_iff h _ _).mpr (mem_primeFormUnitary.mp hA)
  have hcommv : ∀ g ∈ isotropicRadical h (C : Matrix (Fin n) (Fin n) K) W, ∀ v,
      Am *ᵥ (((g : gramSU h _) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v =
        (((g : gramSU h _) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ Am *ᵥ v := by
    intro g hg v
    rw [mulVec_mulVec, mulVec_mulVec, hAm, ← Units.val_mul, ← Units.val_mul, hcomm g hg]
  have htrans : ∀ w ∈ W, ∀ v, Hf w v • Am *ᵥ w = Hf w (Am *ᵥ v) • w := by
    intro w hw v
    obtain ⟨t, ht, htv⟩ := transvection_mem_radical h hC hWiso hw (one_mem h.fixedField)
    have h1 := hcommv t ht v
    rw [htv, htv, mulVec_add, mulVec_smul, one_mul, one_mul] at h1
    exact add_left_cancel h1
  obtain ⟨w₀, hw₀, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hline : ∀ w ∈ W, ∃ c : K, Am *ᵥ w = c • w := by
    intro w hw
    by_cases hw0 : w = 0
    · exact ⟨0, by rw [hw0, mulVec_zero, smul_zero]⟩
    obtain ⟨x, hx⟩ := exists_gramForm_ne_zero h (C := C) hw0
    refine ⟨(Hf w x)⁻¹ * Hf w (Am *ᵥ x), ?_⟩
    rw [mul_smul, ← htrans w hw x, smul_smul, inv_mul_cancel₀ hx, one_smul]
  have hmaps : ∀ w ∈ W, Am.mulVecLin w ∈ W := by
    intro w hw
    obtain ⟨c, hc⟩ := hline w hw
    rw [mulVecLin_apply, hc]
    exact W.smul_mem c hw
  obtain ⟨μ, hμ⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (f := Am.mulVecLin.restrict hmaps) fun w => by
      obtain ⟨c, hc⟩ := hline w w.2
      rw [LinearIndependent.pair_iff]
      push Not
      refine ⟨c, -1, ?_, by norm_num⟩
      apply Subtype.ext
      simp only [Submodule.coe_add, Submodule.coe_smul, LinearMap.coe_restrict_apply,
        mulVecLin_apply, hc, ZeroMemClass.coe_zero]
      rw [neg_one_smul, add_neg_cancel]
  have hAW : ∀ w ∈ W, Am *ᵥ w = μ • w := by
    intro w hw
    have h1 := congrArg Subtype.val (LinearMap.congr_fun hμ ⟨w, hw⟩)
    simpa using h1
  obtain ⟨x₀, hx₀⟩ := exists_gramForm_ne_zero h (C := C) hw₀0
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    have h1 := hAW w₀ hw₀
    rw [zero_smul] at h1
    apply hw₀0
    have h2 : ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (Am *ᵥ w₀) = w₀ := by
      rw [mulVec_mulVec, hAm, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    rw [← h2, h1, mulVec_zero]
  have hAv : ∀ v, μ * Hf w₀ v = Hf w₀ (Am *ᵥ v) := by
    intro v
    have h1 := htrans w₀ hw₀ v
    rw [hAW w₀ hw₀, smul_smul] at h1
    have h2 := sub_eq_zero.mpr h1
    rw [← sub_smul] at h2
    have h3 := sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hw₀0)
    rw [mul_comm] at h3
    exact h3
  have hN : h.norm μ = 1 := by
    have h1 := hAiso w₀ x₀
    rw [hAW w₀ hw₀, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, ← hAv x₀, ← mul_assoc] at h1
    rw [UnitaryFieldData.norm, mul_comm]
    exact mul_right_cancel₀ hx₀ (h1.trans (one_mul _).symm)
  set u : Kˣ := Units.mk0 μ hμ0 with hu
  set A' := GeneralLinearGroup.scalar (Fin n) u⁻¹ * A with hA'def
  have hA'v : ∀ v, (A' : Matrix (Fin n) (Fin n) K) *ᵥ v = μ⁻¹ • (Am *ᵥ v) := by
    intro v
    rw [hA'def, Units.val_mul, GeneralLinearGroup.coe_scalar, ← mulVec_mulVec, scalar_fin_mulVec,
      hu, Units.val_inv_eq_inv_val, Units.val_mk0]
  have hA'W : ∀ w ∈ W, (A' : Matrix (Fin n) (Fin n) K) *ᵥ w = w := by
    intro w hw
    rw [hA'v, hAW w hw, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
  have hNinv : h.bar μ⁻¹ * μ⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, mul_comm, ← UnitaryFieldData.norm, hN, inv_one]
  have hA'iso : ∀ x y, Hf ((A' : Matrix (Fin n) (Fin n) K) *ᵥ x)
      ((A' : Matrix (Fin n) (Fin n) K) *ᵥ y) = Hf x y := by
    intro x y
    rw [hA'v, hA'v]
    simp only [map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [hAiso, ← mul_assoc, mul_comm μ⁻¹, hNinv, one_mul]
  have hA'comm : ∀ g ∈ isotropicRadical h (C : Matrix (Fin n) (Fin n) K) W, ∀ v,
      (A' : Matrix (Fin n) (Fin n) K) *ᵥ (((g : gramSU h _) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ v = (((g : gramSU h _) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) *ᵥ (A' : Matrix (Fin n) (Fin n) K) *ᵥ v := by
    intro g hg v
    rw [hA'v, hA'v, hcommv g hg v, mulVec_smul]
  have hA'L : ∀ v, (A' : Matrix (Fin n) (Fin n) K) *ᵥ v - v ∈ W.orthogonalBilin Hf := by
    intro v
    refine Submodule.mem_orthogonalBilin.mpr fun w hw => ?_
    rw [map_sub, ← hA'iso w v, hA'W w hw, sub_self]
  have hA'LW : ∀ y ∈ W.orthogonalBilin Hf, (A' : Matrix (Fin n) (Fin n) K) *ᵥ y - y ∈ W := by
    intro y hy
    have hyy : -Hf y y ∈ h.fixedField := by
      refine neg_mem (h.mem_fixedField.mpr ?_)
      exact hH.eq y y
    obtain ⟨c, hc⟩ := h.traceLin_surjective ⟨_, hyy⟩
    have hc' : c + h.bar c = -Hf y y := congrArg Subtype.val hc
    have hE := eichler_mem_radical hH hWiso hw₀ hy hc'
    have h1 := hA'comm _ hE x₀
    change (A' : Matrix (Fin n) (Fin n) K) *ᵥ (eichlerMatrix h _ w₀ y c *ᵥ x₀) =
      eichlerMatrix h _ w₀ y c *ᵥ ((A' : Matrix (Fin n) (Fin n) K) *ᵥ x₀) at h1
    have ha' : Hf w₀ ((A' : Matrix (Fin n) (Fin n) K) *ᵥ x₀) = Hf w₀ x₀ := by
      rw [← hA'iso w₀ x₀, hA'W w₀ hw₀]
    rw [eichlerMatrix_mulVec, eichlerMatrix_mulVec, ha', mulVec_add, mulVec_sub, mulVec_add,
      mulVec_smul, mulVec_smul, mulVec_smul, hA'W w₀ hw₀] at h1
    have h2 : Hf w₀ x₀ • ((A' : Matrix (Fin n) (Fin n) K) *ᵥ y - y) =
        (Hf y x₀ - Hf y ((A' : Matrix (Fin n) (Fin n) K) *ᵥ x₀)) • w₀ := by
      rw [smul_sub, sub_smul]
      linear_combination (norm := module) h1
    have h3 : (A' : Matrix (Fin n) (Fin n) K) *ᵥ y - y =
        ((Hf w₀ x₀)⁻¹ * (Hf y x₀ - Hf y ((A' : Matrix (Fin n) (Fin n) K) *ᵥ x₀))) • w₀ := by
      rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hx₀, one_smul]
    rw [h3]
    exact W.smul_mem _ hw₀
  have hrad : IsRadicalMatrix h (C : Matrix (Fin n) (Fin n) K) W (A' : Matrix (Fin n) (Fin n) K) :=
    ⟨hA'W, hA'LW, hA'L⟩
  have hA'SU : A' ∈ gramSU h (C : Matrix (Fin n) (Fin n) K) :=
    mem_gramSU_iff_isometry.mpr ⟨hA'iso, det_eq_one_of_sub_one_pow_three
      (isRadicalMatrix_sub_one_pow_three h hrad)⟩
  refine ⟨u, by rw [hu, Units.val_mk0]; exact hN, ⟨A', hA'SU⟩, hrad, rfl⟩

end Centralizer

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
