module

public import CFSG.GH74.GLS.Stage2.Final.ModelComps

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup

variable {F : Type} [Field F]

@[expose] def J0 (F : Type) [Field F] : GL (Fin 2) F :=
  ⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by
    ext i j; fin_cases i <;> fin_cases j <;> simp, by
    ext i j; fin_cases i <;> fin_cases j <;> simp⟩

theorem coe_J0 : ((J0 F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl

theorem J0_mul_self : J0 F * J0 F = -1 := by
  apply Units.ext
  rw [Units.val_mul, coe_J0, Units.val_neg, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem det_J0 : ((J0 F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  simp [coe_J0, Matrix.det_fin_two]

theorem exists_sq_add_sq [Finite F] (h2 : (2 : F) ≠ 0) (c : F) : ∃ l m : F, l ^ 2 + m ^ 2 = c := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hodd : Fintype.card F % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one (Fintype.card F) with h | h
    · exfalso
      have hchar : ringChar F = 2 := FiniteField.even_card_iff_char_two.2 h
      apply h2
      have := ringChar.Nat.cast_ringChar (R := F)
      rw [hchar] at this
      simpa using this
    · exact h
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (R := F)
    (f := (Polynomial.X ^ 2 : Polynomial F)) (g := Polynomial.X ^ 2 - Polynomial.C c)
    (Polynomial.degree_X_pow 2) (Polynomial.degree_X_pow_sub_C (by decide) _) hodd
  refine ⟨a, b, ?_⟩
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_C] at hab
  linear_combination hab

@[expose] def cycMat (C : Matrix (Fin 2) (Fin 2) F) (u : Fin 2 → F) : Matrix (Fin 2) (Fin 2) F :=
  !![u 0, (C *ᵥ u) 0; u 1, (C *ᵥ u) 1]

theorem det_cycMat (C : Matrix (Fin 2) (Fin 2) F) (u : Fin 2 → F) :
    (cycMat C u).det = u 0 * (C *ᵥ u) 1 - (C *ᵥ u) 0 * u 1 := by
  simp [cycMat, Matrix.det_fin_two]

theorem cycMat_intertwine {C : Matrix (Fin 2) (Fin 2) F} (hC : C * C = -1) (u : Fin 2 → F) :
    C * cycMat C u = cycMat C u * !![0, -1; 1, 0] := by
  have e00 := congrFun₂ hC 0 0
  have e01 := congrFun₂ hC 0 1
  have e10 := congrFun₂ hC 1 0
  have e11 := congrFun₂ hC 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct]
  · linear_combination u 0 * e00 + u 1 * e01
  · linear_combination u 0 * e10 + u 1 * e11

theorem exists_cyc_vector (h2 : (2 : F) ≠ 0) {C : Matrix (Fin 2) (Fin 2) F} (hC : C * C = -1)
    (hdet : C.det = 1) : ∃ u : Fin 2 → F, (cycMat C u).det ≠ 0 := by
  have e00 := congrFun₂ hC 0 0
  have e01 := congrFun₂ hC 0 1
  have e10 := congrFun₂ hC 1 0
  have e11 := congrFun₂ hC 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  rw [Matrix.det_fin_two] at hdet
  by_cases h10 : C 1 0 = 0
  · by_cases h01 : C 0 1 = 0
    · refine ⟨![1, 1], ?_⟩
      rw [det_cycMat]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h10, h01]
      intro h
      rw [h10, h01] at e00 e11 hdet
      apply h2
      have hh : C 0 0 = C 1 1 := by linear_combination -h
      rw [← hh] at hdet
      linear_combination e00 - hdet
    · refine ⟨![0, 1], ?_⟩
      rw [det_cycMat]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      exact h01
  · refine ⟨![1, 0], ?_⟩
    rw [det_cycMat]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact h10

theorem Cc_comm_R (l m : F) :
    (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F) * !![l, -m; m, l] =
      !![l, -m; m, l] * !![0, -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem ord4_conj_lin [Finite F] (h2 : (2 : F) ≠ 0) {a b : GL (Fin 2) F} (ha : a * a = -1)
    (hb : b * b = -1) (hda : ((a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1)
    (hdb : ((b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1) :
    ∃ x : GL (Fin 2) F, ((x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 ∧
      x * a * x⁻¹ = b := by
  have hA : (a : Matrix (Fin 2) (Fin 2) F) * (a : Matrix (Fin 2) (Fin 2) F) = -1 := by
    have := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F)) ha
    simpa using this
  have hB : (b : Matrix (Fin 2) (Fin 2) F) * (b : Matrix (Fin 2) (Fin 2) F) = -1 := by
    have := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F)) hb
    simpa using this
  obtain ⟨ua, hua⟩ := exists_cyc_vector h2 hA hda
  obtain ⟨ub, hub⟩ := exists_cyc_vector h2 hB hdb
  obtain ⟨l, m, hlm⟩ := exists_sq_add_sq h2
    ((cycMat (b : Matrix (Fin 2) (Fin 2) F) ub).det / (cycMat (a : Matrix (Fin 2) (Fin 2) F) ua).det)
  have hdetR : (!![l, -m; m, l] : Matrix (Fin 2) (Fin 2) F).det = l ^ 2 + m ^ 2 := by
    simp [Matrix.det_fin_two]; ring
  have hdetXa' : ((cycMat (a : Matrix (Fin 2) (Fin 2) F) ua) * !![l, -m; m, l]).det =
      (cycMat (b : Matrix (Fin 2) (Fin 2) F) ub).det := by
    rw [Matrix.det_mul, hdetR, hlm]
    field_simp
  have hint_a : (a : Matrix (Fin 2) (Fin 2) F) *
      ((cycMat (a : Matrix (Fin 2) (Fin 2) F) ua) * !![l, -m; m, l]) =
      ((cycMat (a : Matrix (Fin 2) (Fin 2) F) ua) * !![l, -m; m, l]) * !![0, -1; 1, 0] := by
    rw [← Matrix.mul_assoc, cycMat_intertwine hA, Matrix.mul_assoc, Matrix.mul_assoc,
      Cc_comm_R]
  have hint_b := cycMat_intertwine hB ub
  let XaG : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero
    ((cycMat (a : Matrix (Fin 2) (Fin 2) F) ua) * !![l, -m; m, l]) (by rw [hdetXa']; exact hub)
  let XbG : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero
    (cycMat (b : Matrix (Fin 2) (Fin 2) F) ub) hub
  have hXa : (XaG : Matrix (Fin 2) (Fin 2) F) =
      (cycMat (a : Matrix (Fin 2) (Fin 2) F) ua) * !![l, -m; m, l] := rfl
  have hXb : (XbG : Matrix (Fin 2) (Fin 2) F) = cycMat (b : Matrix (Fin 2) (Fin 2) F) ub := rfl
  have hJ : (((J0 F)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] := rfl
  have h1 : a * XaG = XaG * (J0 F)⁻¹ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hXa, hJ]
    exact hint_a
  have h2' : b * XbG = XbG * (J0 F)⁻¹ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hXb, hJ]
    exact hint_b
  refine ⟨XbG * XaG⁻¹, ?_, ?_⟩
  · have hd : Matrix.GeneralLinearGroup.det XbG = Matrix.GeneralLinearGroup.det XaG := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, hXa, hXb,
        hdetXa']
    have h3 : Matrix.GeneralLinearGroup.det (XbG * XaG⁻¹) = 1 := by
      rw [map_mul, map_inv, hd, mul_inv_cancel]
    have := congrArg (fun u : Fˣ => (u : F)) h3
    rw [Matrix.GeneralLinearGroup.val_det_apply] at this
    simpa using this
  · have h3 : XaG⁻¹ * a * XaG = (J0 F)⁻¹ := by
      rw [mul_assoc, h1, ← mul_assoc, inv_mul_cancel, one_mul]
    calc XbG * XaG⁻¹ * a * (XbG * XaG⁻¹)⁻¹ = XbG * (XaG⁻¹ * a * XaG) * XbG⁻¹ := by group
      _ = XbG * (J0 F)⁻¹ * XbG⁻¹ := by rw [h3]
      _ = b := by rw [← h2']; group

theorem mem_statedSL_two_iff {F₀ : Type} [Field F₀] {g : GL (Fin 2) F₀} :
    g ∈ StatedSL 2 F₀ ↔ (g : Matrix (Fin 2) (Fin 2) F₀).det = 1 :=
  CFSG.Open.StatedAPI.mem_statedSL_iff

theorem phi_negOne [Finite F] {M : ModelData F} (hG : GoodModel M) {F₀ : Type} [Field F₀]
    (φ : ↥M.H2 ≃* ↥(StatedSL 2 F₀)) :
    ((φ ⟨-1, M.neg_one_mem_H2⟩ : ↥(StatedSL 2 F₀)) : GL (Fin 2) F₀) = -1 := by
  have hz : (⟨-1, M.neg_one_mem_H2⟩ : ↥M.H2) ∈ Subgroup.center ↥M.H2 := by
    rw [center_H2_eq' hG]; exact Subgroup.mem_zpowers _
  have hzc : φ ⟨-1, M.neg_one_mem_H2⟩ ∈ Subgroup.center ↥(StatedSL 2 F₀) := by
    rw [← CFSG.LieType.Universal.Unitary.map_center_mulEquiv φ]
    exact ⟨_, hz, rfl⟩
  rw [center_statedSL_eq, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hzc
  obtain ⟨c, hc⟩ := hzc
  have hdet : ((c : F₀)) ^ 2 = 1 := by
    have h1 := (mem_statedSL_two_iff.1 (φ ⟨-1, M.neg_one_mem_H2⟩).2)
    rw [← hc] at h1
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Fin.prod_univ_two, sq] using h1
  have hcc : c * c = 1 := Units.ext (by simpa [sq] using hdet)
  rcases units_sq_eq_one hcc with rfl | rfl
  · exfalso
    have h1 : φ ⟨-1, M.neg_one_mem_H2⟩ = 1 := Subtype.ext (by rw [← hc, map_one]; rfl)
    have h2 : (⟨-1, M.neg_one_mem_H2⟩ : ↥M.H2) = 1 := φ.injective (by rw [h1, map_one])
    have h3 : (-1 : GL (Fin 2) F) = 1 := congrArg Subtype.val h2
    exact ModelData.neg_one_ne_one_gl2 hG.two_ne_zero h3
  · rw [← hc]; exact scalar_neg_one_eq 2

theorem ord4_conj_H2 [Finite F] {M : ModelData F} (hG : GoodModel M) {q : ℕ} (hq : Odd q)
    (hSL : HasSL2Model ↥M.H2 (fun r => r = q)) {a b : ↥M.H2}
    (ha : a * a = ⟨-1, M.neg_one_mem_H2⟩) (hb : b * b = ⟨-1, M.neg_one_mem_H2⟩) :
    ∃ x : ↥M.H2, x * a * x⁻¹ = b := by
  obtain ⟨F₀, iF, fF, hF₀, ⟨φ⟩⟩ := hSL
  have h2₀ : (2 : F₀) ≠ 0 := two_ne_zero_of_odd_card (by rw [hF₀]; exact hq)
  have hz := phi_negOne hG φ
  have hA : ((φ a : ↥(StatedSL 2 F₀)) : GL (Fin 2) F₀) * (φ a : GL (Fin 2) F₀) = -1 := by
    have : φ a * φ a = φ ⟨-1, M.neg_one_mem_H2⟩ := by rw [← map_mul, ha]
    have := congrArg Subtype.val this
    rw [Subgroup.coe_mul] at this
    rw [this]; exact hz
  have hB : ((φ b : ↥(StatedSL 2 F₀)) : GL (Fin 2) F₀) * (φ b : GL (Fin 2) F₀) = -1 := by
    have : φ b * φ b = φ ⟨-1, M.neg_one_mem_H2⟩ := by rw [← map_mul, hb]
    have := congrArg Subtype.val this
    rw [Subgroup.coe_mul] at this
    rw [this]; exact hz
  obtain ⟨X, hXdet, hX⟩ := ord4_conj_lin h2₀ hA hB (mem_statedSL_two_iff.1 (φ a).2)
    (mem_statedSL_two_iff.1 (φ b).2)
  have hXS : X ∈ StatedSL 2 F₀ := mem_statedSL_two_iff.2 hXdet
  refine ⟨φ.symm ⟨X, hXS⟩, ?_⟩
  apply φ.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  exact hX

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
