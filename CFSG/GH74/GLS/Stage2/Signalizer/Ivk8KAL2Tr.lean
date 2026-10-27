module

public import CFSG.GH74.GLS.IVK.L2.FixedPGL

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix CFSG.GorensteinWalter CFSG.GH74.GLS.IVK

theorem kaL2_exists_B_coord {F : Type} [Field F] (a b c d x y : F) (hd : a * d - b * c = 1) :
    !![a, b; c, d] * !![x, a * x + b * y; y, c * x + d * y] =
      !![x, a * x + b * y; y, c * x + d * y] * !![0, -1; 1, a + d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination (-x) * hd | linear_combination (-y) * hd

theorem kaL2_exists_B {F : Type} [Field F] (M : Matrix (Fin 2) (Fin 2) F) (hdet : M.det = 1)
    (hns : ∀ s : F, M ≠ s • (1 : Matrix (Fin 2) (Fin 2) F)) :
    ∃ B : Matrix (Fin 2) (Fin 2) F, B.det ≠ 0 ∧ M * B = B * !![0, -1; 1, M.trace] := by
  have hM := Matrix.eta_fin_two M
  have hd : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by rw [Matrix.det_fin_two] at hdet; exact hdet
  have htr : M.trace = M 0 0 + M 1 1 := Matrix.trace_fin_two M
  have key : ∃ x y : F, x * (M 1 0 * x + M 1 1 * y) - y * (M 0 0 * x + M 0 1 * y) ≠ 0 := by
    by_contra hall
    push Not at hall
    have h1 := hall 1 0
    have h2 := hall 0 1
    have h3 := hall 1 1
    apply hns (M 0 0)
    rw [hM]
    have hc : M 1 0 = 0 := by simpa using h1
    have hb : M 0 1 = 0 := by simpa using h2
    have hda : M 1 1 = M 0 0 := by
      have : M 1 0 + M 1 1 - M 0 0 - M 0 1 = 0 := by linear_combination h3
      rw [hc, hb] at this
      linear_combination this
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hc, hb, hda]
  obtain ⟨x, y, hxy⟩ := key
  refine ⟨!![x, M 0 0 * x + M 0 1 * y; y, M 1 0 * x + M 1 1 * y], ?_, ?_⟩
  · rw [Matrix.det_fin_two]
    simpa [mul_comm] using hxy
  · rw [htr]
    conv_lhs => rw [hM]
    exact kaL2_exists_B_coord _ _ _ _ x y hd

theorem kaL2_trace_fixed {F : Type} [Field F] (hchar : (2 : F) ≠ 0) (σ : F ≃+* F)
    (hodd : Odd (orderOf σ)) (M G : Matrix (Fin 2) (Fin 2) F) (hM : M.det = 1) (hG : G.det ≠ 0)
    (c : F) (h : G * M.map σ = c • (M * G)) : σ M.trace = M.trace := by
  have hσdet : (M.map σ).det = 1 := by
    have := RingHom.map_det σ.toRingHom M
    rw [hM, map_one] at this
    exact this.symm
  have hc : c ^ 2 = 1 := by
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_mul, hσdet, hM] at h1
    simp only [Fintype.card_fin] at h1
    have : G.det * (c ^ 2 - 1) = 0 := by linear_combination (-1 : F) * h1
    rcases mul_eq_zero.mp this with h2 | h2
    · exact absurd h2 hG
    · linear_combination h2
  have hGu : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
  have hGi : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hGu
  have hGi' : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hGu
  have h1 : M.map σ = c • (G⁻¹ * M * G) := by
    calc M.map σ = (G⁻¹ * G) * M.map σ := by rw [hGi, one_mul]
      _ = G⁻¹ * (G * M.map σ) := by rw [mul_assoc]
      _ = G⁻¹ * (c • (M * G)) := by rw [h]
      _ = c • (G⁻¹ * M * G) := by rw [Matrix.mul_smul, mul_assoc]
  have htr : σ M.trace = c * M.trace := by
    have h2 := congrArg Matrix.trace h1
    rw [Matrix.trace_smul, smul_eq_mul] at h2
    have h3 : (G⁻¹ * M * G).trace = M.trace := by
      rw [Matrix.trace_mul_comm, ← mul_assoc, hGi', one_mul]
    rw [h3] at h2
    have h4 : (M.map σ).trace = σ M.trace := by
      simp [Matrix.trace_fin_two]
    rw [← h4]
    exact h2
  have hcc : c = 1 ∨ c = -1 := mul_self_eq_one_iff.mp (by rw [← sq]; exact hc)
  have hpow : ∀ k : ℕ, (σ ^ k) M.trace = c ^ k * M.trace := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hσc : σ c = c := by rcases hcc with rfl | rfl <;> simp
      have hs : (σ ^ (k + 1)) M.trace = σ ((σ ^ k) M.trace) := by rw [pow_succ']; rfl
      rw [hs, ih, map_mul, map_pow, hσc, htr, pow_succ]
      ring
  have hfin := hpow (orderOf σ)
  rw [pow_orderOf_eq_one] at hfin
  have hfin' : M.trace = c ^ orderOf σ * M.trace := by simpa using hfin
  rcases hcc with rfl | rfl
  · simpa using htr
  · rw [Odd.neg_one_pow hodd] at hfin'
    have h2 : (2 : F) * M.trace = 0 := by linear_combination hfin'
    have h3 : M.trace = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h hchar
      · exact h
    rw [h3, map_zero]

theorem kaL2_det_ne_zero {F : Type} [Field F] (G : GL (Fin 2) F) : G.val.det ≠ 0 := by
  have := (Matrix.GeneralLinearGroup.det G).ne_zero
  rwa [Matrix.GeneralLinearGroup.val_det_apply] at this

theorem kaL2_matrix_rel {F : Type} [Field F] (σ : F ≃+* F) (G : GL (Fin 2) F)
    (M : Matrix.SpecialLinearGroup (Fin 2) F)
    (h : Matrix.ProjGenLinGroup.mk G * pgl2FieldAut F σ (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (QuotientGroup.mk M : PSL2 F)) * (Matrix.ProjGenLinGroup.mk G)⁻¹ =
      Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk M : PSL2 F)) :
    ∃ c : F, G.val * (M : Matrix (Fin 2) (Fin 2) F).map σ =
        c • ((M : Matrix (Fin 2) (Fin 2) F) * G.val) := by
  have e1 : Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk M : PSL2 F) =
      (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) F))) (Matrix.SpecialLinearGroup.toGL M) :=
    rfl
  have e2 : pgl2FieldAut F σ ((QuotientGroup.mk' (Subgroup.center (GL (Fin 2) F)))
      (Matrix.SpecialLinearGroup.toGL M)) =
      (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) F)))
        (Matrix.GeneralLinearGroup.map σ.toRingHom (Matrix.SpecialLinearGroup.toGL M)) :=
    pgl2RingEquiv_mk σ _
  rw [e1, e2] at h
  have h1 : (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) F)))
      (G * Matrix.GeneralLinearGroup.map σ.toRingHom (Matrix.SpecialLinearGroup.toGL M) * G⁻¹) =
      (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) F))) (Matrix.SpecialLinearGroup.toGL M) := by
    rw [map_mul, map_mul, map_inv]
    exact h
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
  obtain ⟨s, hs⟩ := h1
  set Mσ := Matrix.GeneralLinearGroup.map σ.toRingHom (Matrix.SpecialLinearGroup.toGL M)
    with hMσ
  have hN : G * Mσ * G⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) s =
      Matrix.SpecialLinearGroup.toGL M := by
    rw [hs]; group
  have hc := Matrix.GeneralLinearGroup.scalar_commute s G
  have hN2 : G * Mσ * Matrix.GeneralLinearGroup.scalar (Fin 2) s =
      Matrix.SpecialLinearGroup.toGL M * G := by
    calc G * Mσ * Matrix.GeneralLinearGroup.scalar (Fin 2) s
        = G * Mσ * G⁻¹ * (G * Matrix.GeneralLinearGroup.scalar (Fin 2) s) := by group
      _ = G * Mσ * G⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 2) s * G) := by rw [hc]
      _ = (G * Mσ * G⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) s) * G := by group
      _ = Matrix.SpecialLinearGroup.toGL M * G := by rw [hN]
  have hMat : (G : Matrix (Fin 2) (Fin 2) F) * (Mσ : Matrix (Fin 2) (Fin 2) F) *
      (s : F) • (1 : Matrix (Fin 2) (Fin 2) F) =
      (M : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F)) hN2
    simpa [Matrix.GeneralLinearGroup.scalar, Matrix.smul_one_eq_diagonal] using this
  have hMσ' : (Mσ : Matrix (Fin 2) (Fin 2) F) = (M : Matrix (Fin 2) (Fin 2) F).map σ := by
    ext i j
    exact Matrix.GeneralLinearGroup.map_apply σ.toRingHom i j (Matrix.SpecialLinearGroup.toGL M)
  have h3 : (s : F) • ((G : Matrix (Fin 2) (Fin 2) F) * (Mσ : Matrix (Fin 2) (Fin 2) F)) =
      (M : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) := by
    rw [← hMat, Matrix.mul_smul, mul_one]
  have hs0 : (s : F) ≠ 0 := s.ne_zero
  refine ⟨((s⁻¹ : Fˣ) : F), ?_⟩
  rw [← hMσ', ← h3, smul_smul, Units.val_inv_eq_inv_val, inv_mul_cancel₀ hs0, one_smul]

theorem kaL2_order_dvd {F : Type} [Field F] [Finite F] (hchar : (2 : F) ≠ 0) (σ : F ≃+* F)
    (hodd : Odd (orderOf σ)) (g : PGL2 F) (y : PSL2 F) (hy : y ≠ 1)
    (h : g * pgl2FieldAut F σ (Matrix.ProjectiveSpecialLinearGroup.toPGL y) * g⁻¹ =
      Matrix.ProjectiveSpecialLinearGroup.toPGL y) :
    orderOf y ∣ Nat.card (fixedField σ) * (Nat.card (fixedField σ) ^ 2 - 1) := by
  obtain ⟨M, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨G, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨c, hrel⟩ := kaL2_matrix_rel σ G M h
  have hG := kaL2_det_ne_zero G
  have hM : (M : Matrix (Fin 2) (Fin 2) F).det = 1 := M.2
  have hτ := kaL2_trace_fixed hchar σ hodd _ _ hM hG c hrel
  have hns : ∀ s : F, (M : Matrix (Fin 2) (Fin 2) F) ≠ s • (1 : Matrix (Fin 2) (Fin 2) F) := by
    intro s hs
    apply hy
    have hs2 : s ^ Fintype.card (Fin 2) = 1 := by
      have := hM
      rw [hs, Matrix.det_smul, Matrix.det_one, mul_one] at this
      exact this
    have hcen : M ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [Matrix.SpecialLinearGroup.mem_center_iff]
      exact ⟨s, hs2, by rw [hs, Matrix.smul_one_eq_diagonal]; rfl⟩
    exact (QuotientGroup.eq_one_iff M).mpr hcen
  obtain ⟨B, hB, hMB⟩ := kaL2_exists_B (M : Matrix (Fin 2) (Fin 2) F) hM hns
  have hτ' : (M : Matrix (Fin 2) (Fin 2) F).trace ∈ fixedField σ :=
    (mem_fixedField_iff σ _).mpr hτ
  have hdetC : (!![0, -1; 1, (⟨(M : Matrix (Fin 2) (Fin 2) F).trace, hτ'⟩ : fixedField σ)] :
      Matrix (Fin 2) (Fin 2) (fixedField σ)).det ≠ 0 := by
    simp [Matrix.det_fin_two]
  let C₁ : GL (Fin 2) (fixedField σ) := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdetC
  let Bu : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero B hB
  have hCmat : ((Matrix.GeneralLinearGroup.map (fixedField σ).subtype C₁ : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, (M : Matrix (Fin 2) (Fin 2) F).trace] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.map_apply, C₁, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have hrel2 : Matrix.SpecialLinearGroup.toGL M * Bu =
      Bu * Matrix.GeneralLinearGroup.map (fixedField σ).subtype C₁ := by
    apply Units.ext
    simp only [Units.val_mul, hCmat]
    exact hMB
  have hconj : Matrix.SpecialLinearGroup.toGL M =
      Bu * Matrix.GeneralLinearGroup.map (fixedField σ).subtype C₁ * Bu⁻¹ := by
    rw [← hrel2]; group
  have hy1 : orderOf (QuotientGroup.mk M : PSL2 F) =
      orderOf ((QuotientGroup.mk' (Subgroup.center (GL (Fin 2) F)))
        (Matrix.SpecialLinearGroup.toGL M)) :=
    (orderOf_injective _ Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
      (QuotientGroup.mk M : PSL2 F)).symm
  have hy2 : orderOf ((QuotientGroup.mk' (Subgroup.center (GL (Fin 2) F)))
      (Matrix.SpecialLinearGroup.toGL M)) =
      orderOf ((QuotientGroup.mk' (Subgroup.center (GL (Fin 2) F)))
        (Matrix.GeneralLinearGroup.map (fixedField σ).subtype C₁)) := by
    rw [hconj, map_mul, map_mul, map_inv]
    exact orderOf_injective
      (MulAut.conj ((QuotientGroup.mk' (Subgroup.center (GL (Fin 2) F))) Bu)).toMonoidHom
      (MulAut.conj _).injective _
  have hy3 : (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) F)))
      (Matrix.GeneralLinearGroup.map (fixedField σ).subtype C₁) ∈ (pgl2Incl σ).range :=
    ⟨Matrix.ProjGenLinGroup.mk C₁, pgl2Incl_mk σ C₁⟩
  have hdvd := Subgroup.orderOf_dvd_natCard _ hy3
  have hcard : Nat.card ↥(pgl2Incl σ).range =
      Nat.card (fixedField σ) * (Nat.card (fixedField σ) ^ 2 - 1) := card_range_pgl2Incl σ
  rw [hy1, hy2]
  exact hcard ▸ hdvd

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
