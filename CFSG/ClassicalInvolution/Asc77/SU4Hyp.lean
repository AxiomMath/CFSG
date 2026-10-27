module

public import CFSG.ClassicalInvolution.Phan.Blocks

public section

namespace CFSG.ClassicalInvolution.RouteD.SU4Pattern

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.Phan

variable {K : Type} [Field K] (σ : K ≃+* K)

section Plane

private theorem exists_smul_of_det_eq_zero {p r : Fin 2 → K} (hp : p ≠ 0)
    (h : p 0 * r 1 - p 1 * r 0 = 0) : ∃ l : K, r = l • p := by
  by_cases h0 : p 0 = 0
  · have h1 : p 1 ≠ 0 := fun h1 => hp (by
      funext i
      fin_cases i <;> simp [h0, h1])
    have hr0 : r 0 = 0 := by
      rw [h0] at h
      have : p 1 * r 0 = 0 := by linear_combination -h
      exact (mul_eq_zero.1 this).resolve_left h1
    refine ⟨r 1 / p 1, ?_⟩
    funext i
    fin_cases i
    · simp [hr0, h0]
    · simp [h1]
  · refine ⟨r 0 / p 0, ?_⟩
    funext i
    fin_cases i
    · simp [h0]
    · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination h

theorem exists_hyperbolic_eigenpair (h2 : (2 : K) ≠ 0) {a : K} (ha : σ a * a = -1)
    {B : Matrix (Fin 2) (Fin 2) K} (hiso : conjTr σ B * B = 1)
    (hsq : B * B = a ^ 2 • (1 : Matrix (Fin 2) (Fin 2) K)) (hn₁ : B ≠ a • 1)
    (hn₂ : B ≠ (-a) • 1) :
    ∃ v w : Fin 2 → K, B *ᵥ v = a • v ∧ B *ᵥ w = (-a) • w ∧ herm σ v v = 0 ∧
      herm σ w w = 0 ∧ herm σ v w = 1 := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  set Pp : Matrix (Fin 2) (Fin 2) K := B + a • 1 with hPp
  set Pm : Matrix (Fin 2) (Fin 2) K := B - a • 1 with hPm
  have hmp : Pm * Pp = 0 := by
    have : Pm * Pp = B * B - a ^ 2 • 1 := by
      rw [hPm, hPp]
      simp only [sub_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
        Matrix.one_mul, smul_smul, sq]
      abel
    rw [this, hsq, sub_self]
  have hpm : Pp * Pm = 0 := by
    have : Pp * Pm = B * B - a ^ 2 • 1 := by
      rw [hPm, hPp]
      simp only [add_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
        Matrix.one_mul, smul_smul, sq]
      abel
    rw [this, hsq, sub_self]
  have hPp0 : Pp ≠ 0 := by
    intro h0
    apply hn₂
    rw [neg_smul, eq_neg_iff_add_eq_zero]
    exact h0
  have hPm0 : Pm ≠ 0 := by
    intro h0
    apply hn₁
    rw [sub_eq_zero] at h0
    exact h0
  have mat_ext : ∀ M N : Matrix (Fin 2) (Fin 2) K, (∀ y : Fin 2 → K, M *ᵥ y = N *ᵥ y) → M = N := by
    intro M N h
    exact Matrix.toLin'.injective (LinearMap.ext h)
  obtain ⟨z, hz⟩ : ∃ z : Fin 2 → K, Pp *ᵥ z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hPp0 (mat_ext _ _ fun y => by rw [hcon y, Matrix.zero_mulVec])
  obtain ⟨z', hz'⟩ : ∃ z : Fin 2 → K, Pm *ᵥ z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hPm0 (mat_ext _ _ fun y => by rw [hcon y, Matrix.zero_mulVec])
  have hv : B *ᵥ (Pp *ᵥ z) = a • (Pp *ᵥ z) := by
    have : Pm *ᵥ (Pp *ᵥ z) = 0 := by rw [Matrix.mulVec_mulVec, hmp, Matrix.zero_mulVec]
    rw [hPm, Matrix.sub_mulVec, sub_eq_zero, Matrix.smul_mulVec, Matrix.one_mulVec] at this
    exact this
  have hw : B *ᵥ (Pm *ᵥ z') = (-a) • (Pm *ᵥ z') := by
    have : Pp *ᵥ (Pm *ᵥ z') = 0 := by rw [Matrix.mulVec_mulVec, hpm, Matrix.zero_mulVec]
    rw [hPp, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, add_eq_zero_iff_eq_neg,
      ← neg_smul] at this
    exact this
  set v : Fin 2 → K := Pp *ᵥ z with hvdef
  set w₀ : Fin 2 → K := Pm *ᵥ z' with hw₀def
  have hisoV : ∀ x y : Fin 2 → K, herm σ (B *ᵥ x) (B *ᵥ y) = herm σ x y := by
    intro x y
    rw [herm_mulVec, hiso, Matrix.one_mulVec]
  have iso_of_eig : ∀ (x : Fin 2 → K) (c : K), B *ᵥ x = c • x → σ c * c = -1 →
      herm σ x x = 0 := by
    intro x c hx hc
    have h := hisoV x x
    rw [hx, herm_smul_left, herm_smul_right, ← mul_assoc, hc] at h
    have : (2 : K) * herm σ x x = 0 := by linear_combination -h
    exact (mul_eq_zero.mp this).resolve_left h2
  have hvv : herm σ v v = 0 := iso_of_eig v a hv ha
  have hww : herm σ w₀ w₀ = 0 := by
    refine iso_of_eig w₀ (-a) hw ?_
    rw [map_neg, neg_mul_neg]
    exact ha
  have hdet : v 0 * w₀ 1 - v 1 * w₀ 0 ≠ 0 := by
    intro hd
    obtain ⟨l, hl⟩ := exists_smul_of_det_eq_zero hz hd
    have h3 : B *ᵥ w₀ = (a * l) • v := by
      rw [hl, Matrix.mulVec_smul, hv, smul_smul, mul_comm]
    rw [hw, hl] at h3
    have h4 : (2 * a * l) • v = 0 := by
      have h5 := sub_eq_zero.2 h3.symm
      convert h5 using 1
      module
    have h6 : 2 * a * l = 0 := (smul_eq_zero.1 h4).resolve_right hz
    have hl0 : l = 0 := (mul_eq_zero.1 (show (2 * a) * l = 0 from h6)).resolve_left
      (mul_ne_zero h2 ha0)
    exact hz' (by rw [hl, hl0, zero_smul])
  have hβ : herm σ v w₀ ≠ 0 := by
    intro hβ0
    have e0 : (v 0 * w₀ 1 - v 1 * w₀ 0) • (Pi.single 0 1 : Fin 2 → K) = w₀ 1 • v - v 1 • w₀ := by
      funext i
      fin_cases i <;> simp <;> ring
    have e1 : (v 0 * w₀ 1 - v 1 * w₀ 0) • (Pi.single 1 1 : Fin 2 → K) = v 0 • w₀ - w₀ 0 • v := by
      funext i
      fin_cases i <;> simp <;> ring
    have c0 : (v 0 * w₀ 1 - v 1 * w₀ 0) * σ (v 0) = 0 := by
      have := congrArg (herm σ v) e0
      rw [herm_smul_right, herm_single_right, herm_sub_right, herm_smul_right, herm_smul_right,
        hvv, hβ0] at this
      simpa using this
    have c1 : (v 0 * w₀ 1 - v 1 * w₀ 0) * σ (v 1) = 0 := by
      have := congrArg (herm σ v) e1
      rw [herm_smul_right, herm_single_right, herm_sub_right, herm_smul_right, herm_smul_right,
        hvv, hβ0] at this
      simpa using this
    have hv0 : v 0 = 0 := by
      have := (mul_eq_zero.mp c0).resolve_left hdet
      exact (map_eq_zero_iff σ σ.injective).mp this
    have hv1 : v 1 = 0 := by
      have := (mul_eq_zero.mp c1).resolve_left hdet
      exact (map_eq_zero_iff σ σ.injective).mp this
    apply hz
    funext i
    fin_cases i <;> simp [hv0, hv1]
  refine ⟨v, (herm σ v w₀)⁻¹ • w₀, hv, ?_, hvv, ?_, ?_⟩
  · rw [Matrix.mulVec_smul, hw, smul_comm]
  · rw [herm_smul_left, herm_smul_right, hww]
    ring
  · rw [herm_smul_right, inv_mul_cancel₀ hβ]

end Plane

section Vectors

@[expose] def vecLow (u : Fin 2 → K) : Fin 4 → K := ![u 0, u 1, 0, 0]

@[expose] def vecHigh (u : Fin 2 → K) : Fin 4 → K := ![0, 0, u 0, u 1]

theorem herm_vecLow_vecLow (u u' : Fin 2 → K) :
    herm σ (vecLow u) (vecLow u') = herm σ u u' := by
  simp [herm, vecLow, Fin.sum_univ_four, Fin.sum_univ_two]

theorem herm_vecHigh_vecHigh (u u' : Fin 2 → K) :
    herm σ (vecHigh u) (vecHigh u') = herm σ u u' := by
  simp [herm, vecHigh, Fin.sum_univ_four, Fin.sum_univ_two]

theorem herm_vecLow_vecHigh (u u' : Fin 2 → K) : herm σ (vecLow u) (vecHigh u') = 0 := by
  simp [herm, vecLow, vecHigh, Fin.sum_univ_four]

theorem herm_vecHigh_vecLow (u u' : Fin 2 → K) : herm σ (vecHigh u) (vecLow u') = 0 := by
  simp [herm, vecLow, vecHigh, Fin.sum_univ_four]

variable {σ}

theorem vecLow_smul (c : K) (u : Fin 2 → K) : vecLow (c • u) = c • vecLow u := by
  funext i
  fin_cases i <;> simp [vecLow]

theorem vecHigh_smul (c : K) (u : Fin 2 → K) : vecHigh (c • u) = c • vecHigh u := by
  funext i
  fin_cases i <;> simp [vecHigh]

theorem blockMat_zero_mulVec_vecLow (A : Matrix (Fin 2) (Fin 2) K) (u : Fin 2 → K) :
    blockMat 4 0 A *ᵥ vecLow u = vecLow (A *ᵥ u) := by
  funext i
  fin_cases i <;>
    simp [blockMat_apply, vecLow, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Fin.sum_univ_two]

theorem blockMat_zero_mulVec_vecHigh (A : Matrix (Fin 2) (Fin 2) K) (u : Fin 2 → K) :
    blockMat 4 0 A *ᵥ vecHigh u = vecHigh u := by
  funext i
  fin_cases i <;>
    simp [blockMat_apply, vecHigh, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem blockMat_two_mulVec_vecHigh (A : Matrix (Fin 2) (Fin 2) K) (u : Fin 2 → K) :
    blockMat 4 2 A *ᵥ vecHigh u = vecHigh (A *ᵥ u) := by
  funext i
  fin_cases i <;>
    simp [blockMat_apply, vecHigh, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem blockMat_two_mulVec_vecLow (A : Matrix (Fin 2) (Fin 2) K) (u : Fin 2 → K) :
    blockMat 4 2 A *ᵥ vecLow u = vecLow u := by
  funext i
  fin_cases i <;>
    simp [blockMat_apply, vecLow, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

variable (σ)

theorem conjTr_mul_eq_herm (cols : Fin 4 → (Fin 4 → K)) (i j : Fin 4) :
    (conjTr σ (Matrix.of cols)ᵀ * (Matrix.of cols)ᵀ) i j = herm σ (cols i) (cols j) := by
  simp [Matrix.mul_apply, conjTr, herm]

theorem gram_eigenbasis (hσ : ∀ c, σ (σ c) = c) {v₁ v₂ w₁ w₂ : Fin 2 → K}
    (hv₁ : herm σ v₁ v₁ = 0) (hv₂ : herm σ v₂ v₂ = 0) (hv : herm σ v₁ v₂ = 1)
    (hw₁ : herm σ w₁ w₁ = 0) (hw₂ : herm σ w₂ w₂ = 0) (hw : herm σ w₁ w₂ = 1) :
    conjTr σ (Matrix.of ![vecHigh w₁, vecLow v₁, vecLow v₂, vecHigh w₂])ᵀ *
        (Matrix.of ![vecHigh w₁, vecLow v₁, vecLow v₂, vecHigh w₂])ᵀ = antidiag 4 := by
  have hv' : herm σ v₂ v₁ = 1 := by rw [herm_conj σ hσ, hv, map_one]
  have hw' : herm σ w₂ w₁ = 1 := by rw [herm_conj σ hσ, hw, map_one]
  ext i j
  rw [conjTr_mul_eq_herm]
  fin_cases i <;> fin_cases j <;>
    simp [antidiag, herm_vecLow_vecLow, herm_vecHigh_vecHigh, herm_vecLow_vecHigh,
      herm_vecHigh_vecLow, hv₁, hv₂, hv, hv', hw₁, hw₂, hw, hw']

end Vectors

theorem exists_witt_eigenbasis (hσ : ∀ c, σ (σ c) = c) (h2 : (2 : K) ≠ 0) {a : K}
    (ha : σ a * a = -1) {H₁ H₂ : Matrix (Fin 2) (Fin 2) K}
    (hiso₁ : conjTr σ H₁ * H₁ = 1) (hsq₁ : H₁ * H₁ = a ^ 2 • (1 : Matrix (Fin 2) (Fin 2) K))
    (hn₁ : H₁ ≠ a • 1) (hn₁' : H₁ ≠ (-a) • 1)
    (hiso₂ : conjTr σ H₂ * H₂ = 1) (hsq₂ : H₂ * H₂ = a ^ 2 • (1 : Matrix (Fin 2) (Fin 2) K))
    (hn₂ : H₂ ≠ a • 1) (hn₂' : H₂ ≠ (-a) • 1) :
    ∃ Q : GL (Fin 4) K,
      conjTr σ (Q : Matrix (Fin 4) (Fin 4) K) * (Q : Matrix (Fin 4) (Fin 4) K) = antidiag 4 ∧
      (∀ r : Fin 4, r = 0 ∨ r = 1 →
        (Q : Matrix (Fin 4) (Fin 4) K) r 0 = 0 ∧ (Q : Matrix (Fin 4) (Fin 4) K) r 3 = 0) ∧
      blockMat 4 0 H₁ * blockMat 4 2 H₂ * (Q : Matrix (Fin 4) (Fin 4) K) =
        (Q : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal ![a, a, -a, -a] := by
  obtain ⟨v₁, v₂, hv₁, hv₂, hiv₁, hiv₂, hv⟩ :=
    exists_hyperbolic_eigenpair σ h2 ha hiso₁ hsq₁ hn₁ hn₁'
  obtain ⟨w₁, w₂, hw₁, hw₂, hiw₁, hiw₂, hw⟩ :=
    exists_hyperbolic_eigenpair σ h2 ha hiso₂ hsq₂ hn₂ hn₂'
  set cols : Fin 4 → (Fin 4 → K) := ![vecHigh w₁, vecLow v₁, vecLow v₂, vecHigh w₂] with hcols
  set Qm : Matrix (Fin 4) (Fin 4) K := (Matrix.of cols)ᵀ with hQm
  have hgram : conjTr σ Qm * Qm = antidiag 4 := gram_eigenbasis σ hσ hiv₁ hiv₂ hv hiw₁ hiw₂ hw
  have hdet : Qm.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hgram
    rw [det_mul, h0, mul_zero] at this
    exact det_antidiag_ne_zero 4 this.symm
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero Qm hdet, hgram, ?_, ?_⟩
  · intro r hr
    rcases hr with rfl | rfl <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, hQm, hcols, vecHigh]
  · have e1 : ∀ c : Fin 4, (blockMat 4 0 H₁ * blockMat 4 2 H₂) *ᵥ cols c =
        (![a, a, -a, -a] c) • cols c := by
      intro c
      rw [← Matrix.mulVec_mulVec]
      fin_cases c
      · show blockMat 4 0 H₁ *ᵥ (blockMat 4 2 H₂ *ᵥ vecHigh w₁) = a • vecHigh w₁
        rw [blockMat_two_mulVec_vecHigh, blockMat_zero_mulVec_vecHigh, hw₁, vecHigh_smul]
      · show blockMat 4 0 H₁ *ᵥ (blockMat 4 2 H₂ *ᵥ vecLow v₁) = a • vecLow v₁
        rw [blockMat_two_mulVec_vecLow, blockMat_zero_mulVec_vecLow, hv₁, vecLow_smul]
      · show blockMat 4 0 H₁ *ᵥ (blockMat 4 2 H₂ *ᵥ vecLow v₂) = (-a) • vecLow v₂
        rw [blockMat_two_mulVec_vecLow, blockMat_zero_mulVec_vecLow, hv₂, vecLow_smul]
      · show blockMat 4 0 H₁ *ᵥ (blockMat 4 2 H₂ *ᵥ vecHigh w₂) = (-a) • vecHigh w₂
        rw [blockMat_two_mulVec_vecHigh, blockMat_zero_mulVec_vecHigh, hw₂, vecHigh_smul]
    show blockMat 4 0 H₁ * blockMat 4 2 H₂ * Qm = Qm * Matrix.diagonal ![a, a, -a, -a]
    ext r c
    rw [Matrix.mul_apply, Matrix.mul_diagonal]
    have := congrFun (e1 c) r
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simpa [hQm, Matrix.mul_apply, mul_comm] using this

end CFSG.ClassicalInvolution.RouteD.SU4Pattern
