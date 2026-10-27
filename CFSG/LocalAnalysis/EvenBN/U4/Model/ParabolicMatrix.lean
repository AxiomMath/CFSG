module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.Torus

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section Entries

theorem unitary_entry {M : Matrix (Fin 4) (Fin 4) K}
    (hM : (M.map h.bar)ᵀ * miyamotoJ4 K * M = miyamotoJ4 K) (i j : Fin 4) :
    h.bar (M 0 i) * M 3 j + h.bar (M 1 i) * M 2 j + h.bar (M 2 i) * M 1 j +
      h.bar (M 3 i) * M 0 j = miyamotoJ4 K i j := by
  rw [← hM]
  simp only [Matrix.mul_apply, Fin.sum_univ_four, Matrix.map_apply, Matrix.transpose_apply]
  simp [miyamotoJ4]
  ring

omit [Field K] in
theorem det_shapeOne {R : Type*} [CommRing R] (M : Matrix (Fin 4) (Fin 4) R) (h02 : M 0 2 = 0)
    (h03 : M 0 3 = 0) (h12 : M 1 2 = 0) (h13 : M 1 3 = 0) :
    M.det = (M 0 0 * M 1 1 - M 0 1 * M 1 0) * (M 2 2 * M 3 3 - M 2 3 * M 3 2) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Fin.succAbove, h02, h03, h12, h13,
    Matrix.submatrix]
  ring

omit [Field K] in
theorem det_shapeTwo {R : Type*} [CommRing R] (M : Matrix (Fin 4) (Fin 4) R) (h01 : M 0 1 = 0)
    (h02 : M 0 2 = 0) (h03 : M 0 3 = 0) (h13 : M 1 3 = 0) (h23 : M 2 3 = 0) :
    M.det = M 0 0 * (M 1 1 * M 2 2 - M 1 2 * M 2 1) * M 3 3 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Fin.succAbove, h01, h02, h03, h13, h23,
    Matrix.submatrix]
  ring

theorem cancel_two {p q r s u v x y : K} (hδ : p * s - q * r ≠ 0)
    (h1 : u * p + v * r = x * p + y * r) (h2 : u * q + v * s = x * q + y * s) :
    u = x ∧ v = y := by
  have e1 : (u - x) * (p * s - q * r) = 0 := by linear_combination s * h1 - r * h2
  have e2 : (v - y) * (p * s - q * r) = 0 := by linear_combination p * h2 - q * h1
  exact ⟨sub_eq_zero.1 ((mul_eq_zero.1 e1).resolve_right hδ),
    sub_eq_zero.1 ((mul_eq_zero.1 e2).resolve_right hδ)⟩

theorem coe_miyamotoIHom (p : Kˣ × Kˣ) :
    ((miyamotoIHom h p : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      diagonal ![(p.1 : K), p.2, (h.bar p.2)⁻¹, (h.bar p.1)⁻¹] := by
  simp [miyamotoIHom, miyamotoDiag]

variable [CharP K 2]

theorem eq_of_add_eq_zero_of_charTwo {x y : K} (e : x + y = 0) : y = x := by
  linear_combination e - x * CharTwo.two_eq_zero (R := K)

theorem lowerUnitriangular_eq {M : Matrix (Fin 4) (Fin 4) K}
    (hU : (M.map h.bar)ᵀ * miyamotoJ4 K * M = miyamotoJ4 K)
    (h00 : M 0 0 = 1) (h01 : M 0 1 = 0) (h02 : M 0 2 = 0) (h03 : M 0 3 = 0) (h11 : M 1 1 = 1)
    (h12 : M 1 2 = 0) (h13 : M 1 3 = 0) (h22 : M 2 2 = 1) (h23 : M 2 3 = 0) (h33 : M 3 3 = 1) :
    M = miyamotoX h (M 1 0) (M 2 1) (M 2 0) (M 3 0) ∧ h.bar (M 2 1) = M 2 1 ∧
      M 3 0 + h.bar (M 3 0) + M 1 0 * h.bar (M 2 0) + h.bar (M 1 0) * M 2 0 = 0 := by
  have e20 := unitary_entry h hU 2 0
  have e10 := unitary_entry h hU 1 0
  have e11 := unitary_entry h hU 1 1
  have e00 := unitary_entry h hU 0 0
  simp [miyamotoJ4, h00, h01, h02, h11, h12, h22] at e20 e10 e11 e00
  have hb : h.bar (M 2 1) = M 2 1 := eq_of_add_eq_zero_of_charTwo e11
  have hk : M 3 2 = h.bar (M 1 0) := by
    have := eq_of_add_eq_zero_of_charTwo e20
    rw [← this, h.bar_bar]
  have he : M 3 1 = h.bar (M 2 0) + h.bar (M 1 0) * M 2 1 := by
    have : h.bar (M 3 1) = M 2 0 + h.bar (M 2 1) * M 1 0 := by
      linear_combination e10 - (M 2 0 + h.bar (M 2 1) * M 1 0) * CharTwo.two_eq_zero (R := K)
    rw [← h.bar_bar (M 3 1), this, map_add, map_mul, h.bar_bar]
    ring
  refine ⟨?_, hb, by linear_combination e00⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [miyamotoX, h00, h01, h02, h03, h11, h12, h13, h22, h23,
    h33, hk, he]

theorem mem_P_of_lowerUnitriangular {g : GL (Fin 4) K} (hg : g ∈ gramSU h (miyamotoJ4 K))
    (h00 : (g : Matrix (Fin 4) (Fin 4) K) 0 0 = 1) (h01 : (g : Matrix (Fin 4) (Fin 4) K) 0 1 = 0)
    (h02 : (g : Matrix (Fin 4) (Fin 4) K) 0 2 = 0) (h03 : (g : Matrix (Fin 4) (Fin 4) K) 0 3 = 0)
    (h11 : (g : Matrix (Fin 4) (Fin 4) K) 1 1 = 1) (h12 : (g : Matrix (Fin 4) (Fin 4) K) 1 2 = 0)
    (h13 : (g : Matrix (Fin 4) (Fin 4) K) 1 3 = 0) (h22 : (g : Matrix (Fin 4) (Fin 4) K) 2 2 = 1)
    (h23 : (g : Matrix (Fin 4) (Fin 4) K) 2 3 = 0) (h33 : (g : Matrix (Fin 4) (Fin 4) K) 3 3 = 1) :
    g ∈ miyamotoP h ∧ ((g : Matrix (Fin 4) (Fin 4) K) 2 1 = 0 → g ∈ miyamotoA2 h) ∧
      ((g : Matrix (Fin 4) (Fin 4) K) 1 0 = 0 → g ∈ miyamotoA1 h) := by
  obtain ⟨hM, hb, hd⟩ := lowerUnitriangular_eq h (mem_gramSU.1 hg).1 h00 h01 h02 h03 h11 h12 h13
    h22 h23 h33
  have hg' := eq_miyamotoXGL h hM
  refine ⟨?_, fun h21 => ?_, fun h10 => ?_⟩
  · rw [hg', miyamotoXGL_mem_P]
    exact ⟨hb, hd⟩
  · rw [hg', miyamotoXGL_mem_A2]
    exact ⟨h21, hd⟩
  · rw [hg', miyamotoXGL_mem_A1]
    refine ⟨h10, hb, (add_bar_eq_zero_iff h).1 ?_⟩
    rw [h10] at hd
    simpa using hd

theorem exists_sq_eq_of_charTwo (δ : K) : ∃ s : K, s ^ 2 = δ ∧ (h.bar δ = δ → h.bar s = s) := by
  have := h.finite
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (by simp [ringChar.eq K 2]) δ
  refine ⟨s, by rw [sq, hs], fun hδ => ?_⟩
  have e : (h.bar s + s) ^ 2 = 0 := by
    have : h.bar s * h.bar s = s * s := by rw [← map_mul, ← hs, hδ]
    linear_combination this + (h.bar s * s + s ^ 2) * CharTwo.two_eq_zero (R := K)
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 e
  exact (eq_of_add_eq_zero_of_charTwo this).symm

theorem bar_eq_of_isometry_two {x y z w ν : K} (hν : ν ≠ 0) (hdet : x * w - y * z = ν)
    (e11 : h.bar x * z + h.bar z * x = 0) (e12 : h.bar x * w + h.bar z * y = ν)
    (e21 : h.bar y * z + h.bar w * x = ν) (e22 : h.bar y * w + h.bar w * y = 0) :
    h.bar x = x ∧ h.bar y = y ∧ h.bar z = z ∧ h.bar w = w := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  subst hdet
  have hx : (h.bar x - x) * (x * w - y * z) = 0 := by
    linear_combination x * e12 + y * e11 - (h.bar x * y * z + x * y * h.bar z) * h2
  have hz : (h.bar z - z) * (x * w - y * z) = 0 := by
    linear_combination z * e12 + w * e11 - (h.bar z * z * y + z * w * h.bar x) * h2
  have hy : (h.bar y - y) * (x * w - y * z) = 0 := by
    linear_combination x * e22 - y * e21 - (y * x * w - y ^ 2 * z) * h2
  have hw : (h.bar w - w) * (x * w - y * z) = 0 := by
    linear_combination w * e21 - z * e22
  exact ⟨sub_eq_zero.1 ((mul_eq_zero.1 hx).resolve_right hν),
    sub_eq_zero.1 ((mul_eq_zero.1 hy).resolve_right hν),
    sub_eq_zero.1 ((mul_eq_zero.1 hz).resolve_right hν),
    sub_eq_zero.1 ((mul_eq_zero.1 hw).resolve_right hν)⟩

end Entries

section Levi

theorem miyamotoI1_le_SU : miyamotoI1 h ≤ gramSU h (miyamotoJ4 K) :=
  (miyamotoI1_le_I h).trans (miyamotoI_le_gramSU h)

theorem miyamotoI2_le_SU : miyamotoI2 h ≤ gramSU h (miyamotoJ4 K) :=
  (miyamotoI2_le_I h).trans (miyamotoI_le_gramSU h)

variable [CharP K 2]

theorem miyamotoN1_le_gramSU : miyamotoN1 h ≤ gramSU h (miyamotoJ4 K) := by
  intro g hg
  obtain ⟨m, hm, hg⟩ := (mem_miyamotoN1 h).1 hg
  have hbb := h.bar_bar
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [Matrix.det_fin_two] at hm
  have hm' : h.bar (m 0 0) * h.bar (m 1 1) - h.bar (m 0 1) * h.bar (m 1 0) = 1 := by
    rw [← map_mul, ← map_mul, ← map_sub, hm, map_one]
  refine mem_gramSU.2 ⟨?_, ?_⟩
  · rw [hg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [miyamotoN1Mat, miyamotoJ4, Matrix.mul_apply, Fin.sum_univ_four, hbb]
    all_goals first
      | linear_combination hm + (m 0 1 * m 1 0) * h2
      | linear_combination hm' + (h.bar (m 0 1) * h.bar (m 1 0)) * h2
      | linear_combination (m 0 0 * m 1 0) * h2
      | linear_combination (m 0 1 * m 1 1) * h2
      | linear_combination (h.bar (m 0 0) * h.bar (m 1 0)) * h2
      | linear_combination (h.bar (m 0 1) * h.bar (m 1 1)) * h2
  · rw [hg, det_shapeOne _ rfl rfl rfl rfl]
    simp [miyamotoN1Mat]
    linear_combination (h.bar (m 0 0) * h.bar (m 1 1) - h.bar (m 0 1) * h.bar (m 1 0)) * hm + hm'

theorem miyamotoN2_le_gramSU : miyamotoN2 h ≤ gramSU h (miyamotoJ4 K) := by
  intro g hg
  obtain ⟨m, hm, hbar, hg⟩ := (mem_miyamotoN2 h).1 hg
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [Matrix.det_fin_two] at hm
  refine mem_gramSU.2 ⟨?_, ?_⟩
  · rw [hg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [miyamotoN2Mat, miyamotoJ4, Matrix.mul_apply, Fin.sum_univ_four, hbar]
    all_goals first
      | linear_combination hm + (m 0 1 * m 1 0) * h2
      | linear_combination (m 0 0 * m 1 0) * h2
      | linear_combination (m 0 1 * m 1 1) * h2
  · rw [hg, det_shapeTwo _ rfl rfl rfl rfl rfl]
    simp [miyamotoN2Mat]
    linear_combination hm

end Levi

section Construct

theorem exists_mem_miyamotoN1_coe_eq {m : Matrix (Fin 2) (Fin 2) K} (hm : m.det = 1) :
    ∃ n ∈ miyamotoN1 h, (n : Matrix (Fin 4) (Fin 4) K) = miyamotoN1Mat h m :=
  ⟨_, ⟨⟨m, hm⟩, rfl⟩, rfl⟩

theorem exists_mem_miyamotoN2_coe_eq {m : Matrix (Fin 2) (Fin 2) K} (hm : m.det = 1)
    (hbar : ∀ i j, h.bar (m i j) = m i j) :
    ∃ n ∈ miyamotoN2 h, (n : Matrix (Fin 4) (Fin 4) K) = miyamotoN2Mat K m := by
  let m' : Matrix (Fin 2) (Fin 2) h.fixedField := fun i j => ⟨m i j, hbar i j⟩
  have hm' : m'.map h.fixedField.subtype = m := by
    ext i j
    rfl
  have hdet : m'.det = 1 := by
    apply h.fixedField.subtype_injective
    rw [h.fixedField.subtype.map_det, RingHom.mapMatrix_apply, hm', hm, map_one]
  refine ⟨_, ⟨⟨m', hdet⟩, rfl⟩, ?_⟩
  rw [← hm']
  rfl

theorem pow_sub_one_mul_sq (a : K) : a ^ (2 ^ f - 1) * a ^ 2 = a * h.bar a := by
  have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  rw [h.bar_apply, ← pow_add, ← pow_succ']
  congr 1
  omega

end Construct

section Decompositions

variable [CharP K 2]

theorem exists_mul_of_lower {g : GL (Fin 4) K} (hg : g ∈ gramSU h (miyamotoJ4 K))
    (h01 : (g : Matrix (Fin 4) (Fin 4) K) 0 1 = 0) (h02 : (g : Matrix (Fin 4) (Fin 4) K) 0 2 = 0)
    (h03 : (g : Matrix (Fin 4) (Fin 4) K) 0 3 = 0) (h12 : (g : Matrix (Fin 4) (Fin 4) K) 1 2 = 0)
    (h13 : (g : Matrix (Fin 4) (Fin 4) K) 1 3 = 0) (h23 : (g : Matrix (Fin 4) (Fin 4) K) 2 3 = 0) :
    ∃ p ∈ miyamotoP h, ∃ d ∈ miyamotoI h, g = p * d := by
  obtain ⟨M, hM⟩ : ∃ M, (g : Matrix (Fin 4) (Fin 4) K) = M := ⟨_, rfl⟩
  rw [hM] at h01 h02 h03 h12 h13 h23
  have hU : (M.map h.bar)ᵀ * miyamotoJ4 K * M = miyamotoJ4 K := hM ▸ (mem_gramSU.1 hg).1
  have hdet : M.det = 1 := hM ▸ (mem_gramSU.1 hg).2
  rw [det_shapeTwo M h01 h02 h03 h13 h23, h12, zero_mul, sub_zero] at hdet
  have e03 := unitary_entry h hU 0 3
  have e12 := unitary_entry h hU 1 2
  simp [miyamotoJ4, h01, h02, h03, h12, h13, h23] at e03 e12
  have h0 : M 0 0 ≠ 0 := fun e => by simp [e] at e03
  have h1 : M 1 1 ≠ 0 := fun e => by simp [e] at e12
  have h2 : M 2 2 ≠ 0 := fun e => by simp [e] at e12
  have h3 : M 3 3 ≠ 0 := fun e => by simp [e] at e03
  have hb0 : h.bar (M 0 0) ≠ 0 := by simpa using h0
  have hb1 : h.bar (M 1 1) ≠ 0 := by simpa using h1
  set d := miyamotoIHom h (Units.mk0 (M 0 0) h0, Units.mk0 (M 1 1) h1) with hd
  have hdm : (d : Matrix (Fin 4) (Fin 4) K) = diagonal ![M 0 0, M 1 1, M 2 2, M 3 3] := by
    rw [hd, coe_miyamotoIHom]
    simp only [Units.val_mk0]
    rw [eq_inv_of_mul_eq_one_right e12, eq_inv_of_mul_eq_one_right e03]
  have hdI : d ∈ miyamotoI h := by
    refine (miyamotoIHom_mem_miyamotoI_iff h _).2 (Units.ext ?_)
    simp only [miyamotoIParam, MonoidHom.mul_apply, MonoidHom.coe_fst, MonoidHom.coe_snd,
      MonoidHom.inv_apply, MonoidHom.coe_comp, Function.comp_apply, Units.val_mul,
      Units.val_inv_eq_inv_val, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_ofClass, Units.val_mk0, Units.val_one]
    rw [← eq_inv_of_mul_eq_one_right e12, ← eq_inv_of_mul_eq_one_right e03]
    linear_combination hdet
  refine ⟨g * d⁻¹, ?_, d, hdI, by rw [inv_mul_cancel_right]⟩
  have hA : ((g * d⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * diagonal ![M 0 0, M 1 1,
      M 2 2, M 3 3] = M := by
    rw [← hdm, ← Units.val_mul, inv_mul_cancel_right, hM]
  have ent : ∀ i j, ((g * d⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j *
      ![M 0 0, M 1 1, M 2 2, M 3 3] j = M i j := fun i j => by
    have := congrFun (congrFun hA i) j
    rwa [Matrix.mul_diagonal] at this
  have one : ∀ {x y : K}, y ≠ 0 → x * y = y → x = 1 := fun hy e =>
    (mul_eq_right₀ hy).1 e
  have zero : ∀ {x y : K}, y ≠ 0 → x * y = 0 → x = 0 := fun hy e =>
    (mul_eq_zero.1 e).resolve_right hy
  have q00 := ent 0 0
  have q01 := ent 0 1
  have q02 := ent 0 2
  have q03 := ent 0 3
  have q11 := ent 1 1
  have q12 := ent 1 2
  have q13 := ent 1 3
  have q22 := ent 2 2
  have q23 := ent 2 3
  have q33 := ent 3 3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three] at q00 q01 q02 q03 q11 q12 q13 q22 q23 q33
  rw [h01] at q01
  rw [h02] at q02
  rw [h03] at q03
  rw [h12] at q12
  rw [h13] at q13
  rw [h23] at q23
  exact (mem_P_of_lowerUnitriangular h (mul_mem hg (inv_mem (miyamotoI_le_gramSU h hdI)))
    (one h0 q00) (zero h1 q01) (zero h2 q02) (zero h3 q03) (one h1 q11) (zero h2 q12)
    (zero h3 q13) (one h2 q22) (zero h3 q23) (one h3 q33)).1

theorem exists_mul_of_shapeOne {g : GL (Fin 4) K} (hg : g ∈ gramSU h (miyamotoJ4 K))
    (h02 : (g : Matrix (Fin 4) (Fin 4) K) 0 2 = 0) (h03 : (g : Matrix (Fin 4) (Fin 4) K) 0 3 = 0)
    (h12 : (g : Matrix (Fin 4) (Fin 4) K) 1 2 = 0) (h13 : (g : Matrix (Fin 4) (Fin 4) K) 1 3 = 0) :
    ∃ a ∈ miyamotoA1 h, ∃ i ∈ miyamotoI1 h, ∃ n ∈ miyamotoN1 h, g = a * i * n := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨M, hM⟩ : ∃ M, (g : Matrix (Fin 4) (Fin 4) K) = M := ⟨_, rfl⟩
  rw [hM] at h02 h03 h12 h13
  have hU : (M.map h.bar)ᵀ * miyamotoJ4 K * M = miyamotoJ4 K := hM ▸ (mem_gramSU.1 hg).1
  have hdet : M.det = 1 := hM ▸ (mem_gramSU.1 hg).2
  rw [det_shapeOne M h02 h03 h12 h13] at hdet
  have e02 := unitary_entry h hU 0 2
  have e03 := unitary_entry h hU 0 3
  have e12 := unitary_entry h hU 1 2
  have e13 := unitary_entry h hU 1 3
  simp [miyamotoJ4, h02, h03, h12, h13] at e02 e03 e12 e13
  have hδ0 : M 0 0 * M 1 1 - M 0 1 * M 1 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have hΔ0 : M 2 2 * M 3 3 - M 2 3 * M 3 2 ≠ 0 := right_ne_zero_of_mul_eq_one hdet
  have hbδ : h.bar (M 0 0 * M 1 1 - M 0 1 * M 1 0) =
      h.bar (M 0 0) * h.bar (M 1 1) - h.bar (M 0 1) * h.bar (M 1 0) := by
    simp only [map_sub, map_mul]
  have z22 : h.bar (M 0 0 * M 1 1 - M 0 1 * M 1 0) * M 2 2 = h.bar (M 0 0) := by
    rw [hbδ]
    linear_combination h.bar (M 0 0) * e12 - h.bar (M 0 1) * e02
  have z32 : h.bar (M 0 0 * M 1 1 - M 0 1 * M 1 0) * M 3 2 = h.bar (M 1 0) := by
    rw [hbδ]
    linear_combination h.bar (M 1 1) * e02 - h.bar (M 1 0) * e12 - h.bar (M 1 0) * h2
  have z33 : h.bar (M 0 0 * M 1 1 - M 0 1 * M 1 0) * M 3 3 = h.bar (M 1 1) := by
    rw [hbδ]
    linear_combination h.bar (M 1 1) * e03 - h.bar (M 1 0) * e13
  have z23 : h.bar (M 0 0 * M 1 1 - M 0 1 * M 1 0) * M 2 3 = h.bar (M 0 1) := by
    rw [hbδ]
    linear_combination h.bar (M 0 0) * e13 - h.bar (M 0 1) * e03 - h.bar (M 0 1) * h2
  have hδF : h.bar (M 0 0 * M 1 1 - M 0 1 * M 1 0) = M 0 0 * M 1 1 - M 0 1 * M 1 0 := by
    set δ := M 0 0 * M 1 1 - M 0 1 * M 1 0
    have hb0 : h.bar δ ≠ 0 := by simpa using hδ0
    have e : h.bar δ * (h.bar δ * (M 2 2 * M 3 3 - M 2 3 * M 3 2)) = h.bar δ * 1 := by
      have : h.bar δ * (h.bar δ * (M 2 2 * M 3 3 - M 2 3 * M 3 2)) =
          (h.bar δ * M 2 2) * (h.bar δ * M 3 3) - (h.bar δ * M 2 3) * (h.bar δ * M 3 2) := by ring
      rw [this, z22, z33, z23, z32, mul_one, hbδ]
    have e' := mul_left_cancel₀ hb0 e
    have e'' : (h.bar δ - δ) * (M 2 2 * M 3 3 - M 2 3 * M 3 2) = 0 := by
      linear_combination e' - hdet
    exact sub_eq_zero.1 ((mul_eq_zero.1 e'').resolve_right hΔ0)
  obtain ⟨s, hs2, hsF⟩ := exists_sq_eq_of_charTwo h (M 0 0 * M 1 1 - M 0 1 * M 1 0)
  have hs : h.bar s = s := hsF hδF
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hδ0 (by rw [← hs2]; ring)
  have hm : (!![M 0 0 / s, M 0 1 / s; M 1 0 / s, M 1 1 / s] : Matrix (Fin 2) (Fin 2) K).det =
      1 := by
    rw [Matrix.det_fin_two_of]
    field_simp
    linear_combination -hs2
  obtain ⟨n, hn, hnm⟩ := exists_mem_miyamotoN1_coe_eq h hm
  set i := miyamotoIHom h (Units.mk0 s hs0, Units.mk0 s hs0) with hi
  have hiI : i ∈ miyamotoI1 h := (mem_miyamotoI1 h).2 ⟨Units.mk0 s hs0, hs, rfl⟩
  have hblock : ∀ {x y : K}, h.bar (M 0 0 * M 1 1 - M 0 1 * M 1 0) * y = h.bar x →
      s⁻¹ * (h.bar x / s) = y := by
    intro x y e
    rw [hδF, ← hs2] at e
    field_simp
    linear_combination -e
  have hℓ : ((i * n : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      !![M 0 0, M 0 1, 0, 0; M 1 0, M 1 1, 0, 0; 0, 0, M 2 2, M 2 3; 0, 0, M 3 2, M 3 3] := by
    rw [Units.val_mul, hnm, hi, coe_miyamotoIHom]
    ext a b
    rw [Matrix.diagonal_mul]
    fin_cases a <;> fin_cases b <;> simp [miyamotoN1Mat, hs, map_div₀]
    all_goals first
      | exact hblock z22
      | exact hblock z23
      | exact hblock z32
      | exact hblock z33
      | field_simp
  refine ⟨g * (i * n)⁻¹, ?_, i, hiI, n, hn, by rw [mul_assoc, inv_mul_cancel_right]⟩
  set A := ((g * (i * n)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hAdef
  have hA : A * !![M 0 0, M 0 1, 0, 0; M 1 0, M 1 1, 0, 0; 0, 0, M 2 2, M 2 3;
      0, 0, M 3 2, M 3 3] = M := by
    rw [hAdef, ← hℓ, ← Units.val_mul, inv_mul_cancel_right, hM]
  have ent : ∀ a b, (A * !![M 0 0, M 0 1, 0, 0; M 1 0, M 1 1, 0, 0; 0, 0, M 2 2, M 2 3;
      0, 0, M 3 2, M 3 3]) a b = M a b := fun a b => by rw [hA]
  have q00 := ent 0 0
  have q01 := ent 0 1
  have q02 := ent 0 2
  have q03 := ent 0 3
  have q10 := ent 1 0
  have q11 := ent 1 1
  have q12 := ent 1 2
  have q13 := ent 1 3
  have q22 := ent 2 2
  have q23 := ent 2 3
  have q32 := ent 3 2
  have q33 := ent 3 3
  simp [Matrix.mul_apply, Fin.sum_univ_four] at q00 q01 q02 q03 q10 q11 q12 q13 q22 q23 q32 q33
  rw [h02] at q02
  rw [h03] at q03
  rw [h12] at q12
  rw [h13] at q13
  obtain ⟨r00, r01⟩ := cancel_two hδ0 (x := 1) (y := 0) (by rw [q00]; ring) (by rw [q01]; ring)
  obtain ⟨r10, r11⟩ := cancel_two hδ0 (x := 0) (y := 1) (by rw [q10]; ring) (by rw [q11]; ring)
  obtain ⟨r02, r03⟩ := cancel_two hΔ0 (x := 0) (y := 0) (by rw [q02]; ring) (by rw [q03]; ring)
  obtain ⟨r12, r13⟩ := cancel_two hΔ0 (x := 0) (y := 0) (by rw [q12]; ring) (by rw [q13]; ring)
  obtain ⟨r22, r23⟩ := cancel_two hΔ0 (x := 1) (y := 0) (by rw [q22]; ring) (by rw [q23]; ring)
  obtain ⟨r32, r33⟩ := cancel_two hΔ0 (x := 0) (y := 1) (by rw [q32]; ring) (by rw [q33]; ring)
  have hAmem : g * (i * n)⁻¹ ∈ gramSU h (miyamotoJ4 K) :=
    mul_mem hg (inv_mem (mul_mem (miyamotoI1_le_SU h hiI) (miyamotoN1_le_gramSU h hn)))
  exact (mem_P_of_lowerUnitriangular h hAmem r00 r01 r02 r03 r11 r12 r13 r22 r23 r33).2.2 r10

theorem exists_mul_of_shapeTwo {g : GL (Fin 4) K} (hg : g ∈ gramSU h (miyamotoJ4 K))
    (h03 : (g : Matrix (Fin 4) (Fin 4) K) 0 3 = 0) (h13 : (g : Matrix (Fin 4) (Fin 4) K) 1 3 = 0)
    (h23 : (g : Matrix (Fin 4) (Fin 4) K) 2 3 = 0) :
    ∃ a ∈ miyamotoA2 h, ∃ i ∈ miyamotoI2 h, ∃ n ∈ miyamotoN2 h, g = a * i * n := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hbb := h.bar_bar
  obtain ⟨M, hM⟩ : ∃ M, (g : Matrix (Fin 4) (Fin 4) K) = M := ⟨_, rfl⟩
  rw [hM] at h03 h13 h23
  have hU : (M.map h.bar)ᵀ * miyamotoJ4 K * M = miyamotoJ4 K := hM ▸ (mem_gramSU.1 hg).1
  have hdet : M.det = 1 := hM ▸ (mem_gramSU.1 hg).2
  have e03 := unitary_entry h hU 0 3
  have e13 := unitary_entry h hU 1 3
  have e23 := unitary_entry h hU 2 3
  simp [miyamotoJ4, h03, h13, h23] at e03 e13 e23
  have h33 : M 3 3 ≠ 0 := right_ne_zero_of_mul_eq_one e03
  have h01 : M 0 1 = 0 := by simpa [h33] using e13
  have h02 : M 0 2 = 0 := by simpa [h33] using e23
  rw [det_shapeTwo M h01 h02 h03 h13 h23] at hdet
  have e11 := unitary_entry h hU 1 1
  have e12 := unitary_entry h hU 1 2
  have e21 := unitary_entry h hU 2 1
  have e22 := unitary_entry h hU 2 2
  simp [miyamotoJ4, h01, h02] at e11 e12 e21 e22
  have hγ0 : M 0 0 ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul_eq_one hdet)
  have hΔ0 : M 1 1 * M 2 2 - M 1 2 * M 2 1 ≠ 0 :=
    right_ne_zero_of_mul (left_ne_zero_of_mul_eq_one hdet)
  have hbγ : h.bar (M 0 0) ≠ 0 := by simpa using hγ0
  have h33' : M 3 3 = (h.bar (M 0 0))⁻¹ := eq_inv_of_mul_eq_one_right e03
  have hΔ : M 0 0 ^ 2 * (M 1 1 * M 2 2 - M 1 2 * M 2 1) = M 0 0 * h.bar (M 0 0) := by
    rw [h33'] at hdet
    field_simp at hdet
    linear_combination M 0 0 * hdet
  obtain ⟨fx, fy, fz, fw⟩ := bar_eq_of_isometry_two h (x := M 0 0 * M 1 1) (y := M 0 0 * M 1 2)
    (z := M 0 0 * M 2 1) (w := M 0 0 * M 2 2) (ν := M 0 0 * h.bar (M 0 0)) (mul_ne_zero hγ0 hbγ)
    (by linear_combination hΔ)
    (by simp only [map_mul]; linear_combination h.bar (M 0 0) * M 0 0 * e11)
    (by simp only [map_mul]; linear_combination h.bar (M 0 0) * M 0 0 * e12)
    (by simp only [map_mul]; linear_combination h.bar (M 0 0) * M 0 0 * e21)
    (by simp only [map_mul]; linear_combination h.bar (M 0 0) * M 0 0 * e22)
  obtain ⟨a₀, ha₀, -⟩ := exists_sq_eq_of_charTwo h (M 0 0)
  have ha₀0 : a₀ ≠ 0 := by
    rintro rfl
    exact hγ0 (by rw [← ha₀]; ring)
  have hba₀ : h.bar a₀ ≠ 0 := by simpa using ha₀0
  have hN : h.bar (a₀ * h.bar a₀) = a₀ * h.bar a₀ := by rw [map_mul, hbb, mul_comm]
  have hN0 : a₀ * h.bar a₀ ≠ 0 := mul_ne_zero ha₀0 hba₀
  have hm : (!![M 0 0 * M 1 1 / (a₀ * h.bar a₀), M 0 0 * M 1 2 / (a₀ * h.bar a₀);
      M 0 0 * M 2 1 / (a₀ * h.bar a₀), M 0 0 * M 2 2 / (a₀ * h.bar a₀)] :
        Matrix (Fin 2) (Fin 2) K).det = 1 := by
    have hγ' : M 0 0 * h.bar (M 0 0) = (a₀ * h.bar a₀) ^ 2 := by
      rw [← ha₀, map_pow]
      ring
    rw [Matrix.det_fin_two_of]
    field_simp
    linear_combination hΔ + hγ'
  obtain ⟨n, hn, hnm⟩ := exists_mem_miyamotoN2_coe_eq h hm (fun i j => by
    fin_cases i <;> fin_cases j <;> simp [map_div₀, hN, fx, fy, fz, fw])
  set i := miyamotoI2Hom h (Units.mk0 a₀ ha₀0) with hi
  have hiI : i ∈ miyamotoI2 h := ⟨_, rfl⟩
  have hlam : a₀ ^ (2 ^ f - 1) * M 0 0 = a₀ * h.bar a₀ := by
    rw [← ha₀, pow_sub_one_mul_sq]
  have hℓ : ((i * n : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      !![M 0 0, 0, 0, 0; 0, M 1 1, M 1 2, 0; 0, M 2 1, M 2 2, 0; 0, 0, 0, M 3 3] := by
    rw [Units.val_mul, hnm, hi, miyamotoI2Hom_eq, coe_miyamotoIHom]
    ext a b
    rw [Matrix.diagonal_mul]
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [bar_pow_sub_one h ha₀0, inv_inv]
    fin_cases a <;> fin_cases b <;> simp [miyamotoN2Mat, ha₀, h33']
    all_goals field_simp
    all_goals first
      | linear_combination M 1 1 * hlam
      | linear_combination M 1 2 * hlam
      | linear_combination M 2 1 * hlam
      | linear_combination M 2 2 * hlam
  refine ⟨g * (i * n)⁻¹, ?_, i, hiI, n, hn, by rw [mul_assoc, inv_mul_cancel_right]⟩
  set A := ((g * (i * n)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hAdef
  have hA : A * !![M 0 0, 0, 0, 0; 0, M 1 1, M 1 2, 0; 0, M 2 1, M 2 2, 0; 0, 0, 0, M 3 3] = M := by
    rw [hAdef, ← hℓ, ← Units.val_mul, inv_mul_cancel_right, hM]
  have ent : ∀ a b, (A * !![M 0 0, 0, 0, 0; 0, M 1 1, M 1 2, 0; 0, M 2 1, M 2 2, 0;
      0, 0, 0, M 3 3]) a b = M a b := fun a b => by rw [hA]
  have q00 := ent 0 0
  have q01 := ent 0 1
  have q02 := ent 0 2
  have q03 := ent 0 3
  have q11 := ent 1 1
  have q12 := ent 1 2
  have q13 := ent 1 3
  have q21 := ent 2 1
  have q22 := ent 2 2
  have q23 := ent 2 3
  have q33 := ent 3 3
  simp [Matrix.mul_apply, Fin.sum_univ_four] at q00 q01 q02 q03 q11 q12 q13 q21 q22 q23 q33
  rw [h01] at q01
  rw [h02] at q02
  rw [h03] at q03
  rw [h13] at q13
  rw [h23] at q23
  have one : ∀ {x y : K}, y ≠ 0 → x * y = y → x = 1 := fun hy e => (mul_eq_right₀ hy).1 e
  have zero : ∀ {x y : K}, y ≠ 0 → x * y = 0 → x = 0 := fun hy e =>
    (mul_eq_zero.1 e).resolve_right hy
  obtain ⟨r01, r02⟩ := cancel_two hΔ0 (x := 0) (y := 0) (by rw [q01]; ring) (by rw [q02]; ring)
  obtain ⟨r11, r12⟩ := cancel_two hΔ0 (x := 1) (y := 0) (by rw [q11]; ring) (by rw [q12]; ring)
  obtain ⟨r21, r22⟩ := cancel_two hΔ0 (x := 0) (y := 1) (by rw [q21]; ring) (by rw [q22]; ring)
  have hAmem : g * (i * n)⁻¹ ∈ gramSU h (miyamotoJ4 K) :=
    mul_mem hg (inv_mem (mul_mem (miyamotoI2_le_SU h hiI) (miyamotoN2_le_gramSU h hn)))
  exact (mem_P_of_lowerUnitriangular h hAmem (one hγ0 q00) r01 r02 (zero h33 q03) r11 r12
    (zero h33 q13) r22 (zero h33 q23) (one h33 q33)).2.1 r21

end Decompositions

section Shapes

theorem conj_mem_centerIn {G : Type*} [Group G] {H : Subgroup G} {g x : G}
    (hg : g ∈ normalizer (H : Set G)) (hx : x ∈ CFSG.centerIn H) :
    g * x * g⁻¹ ∈ CFSG.centerIn H := by
  obtain ⟨hxH, hxC⟩ := hx
  refine ⟨(mem_normalizer_iff.1 hg x).1 hxH, mem_centralizer_iff.2 fun y hy => ?_⟩
  have hy' : g⁻¹ * y * g ∈ H := (mem_normalizer_iff''.1 hg y).1 hy
  have e := mem_centralizer_iff.1 hxC _ hy'
  calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [e]
    _ = g * x * g⁻¹ * y := by group

theorem normalizer_le_normalizer_centerIn {G : Type*} [Group G] (H : Subgroup G) :
    normalizer (H : Set G) ≤ normalizer (CFSG.centerIn H : Set G) := by
  intro g hg
  refine mem_normalizer_iff.2 fun x => ⟨fun hx => conj_mem_centerIn hg hx, fun hx => ?_⟩
  have := conj_mem_centerIn (inv_mem hg) hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at this

theorem shapeTwo_of_mem_normalizer_Z {g : GL (Fin 4) K}
    (hg : g ∈ normalizer (miyamotoZ h : Set (GL (Fin 4) K))) :
    (g : Matrix (Fin 4) (Fin 4) K) 0 3 = 0 ∧ (g : Matrix (Fin 4) (Fin 4) K) 1 3 = 0 ∧
      (g : Matrix (Fin 4) (Fin 4) K) 2 3 = 0 := by
  have hz : miyamotoXGL h 0 0 0 1 ∈ miyamotoZ h := ⟨1, map_one _, rfl⟩
  obtain ⟨d, -, e⟩ := (mem_normalizer_iff.1 hg _).1 hz
  have e' : g * miyamotoXGL h 0 0 0 1 = miyamotoXGL h 0 0 0 d * g := by
    rw [← e, inv_mul_cancel_right]
  have ent : ∀ i j, ((g : Matrix (Fin 4) (Fin 4) K) * miyamotoX h 0 0 0 1) i j =
      (miyamotoX h 0 0 0 d * (g : Matrix (Fin 4) (Fin 4) K)) i j := fun i j => by
    rw [← coe_miyamotoXGL, ← coe_miyamotoXGL, ← Units.val_mul, ← Units.val_mul, e']
  have q0 := ent 0 0
  have q1 := ent 1 0
  have q2 := ent 2 0
  simp [Matrix.mul_apply, Fin.sum_univ_four, miyamotoX] at q0 q1 q2
  exact ⟨q0, q1, q2⟩

theorem shapeOne_of_mem_normalizer_A1 [CharP K 2] {g : GL (Fin 4) K}
    (hg : g ∈ normalizer (miyamotoA1 h : Set (GL (Fin 4) K))) :
    (g : Matrix (Fin 4) (Fin 4) K) 0 2 = 0 ∧ (g : Matrix (Fin 4) (Fin 4) K) 0 3 = 0 ∧
      (g : Matrix (Fin 4) (Fin 4) K) 1 2 = 0 ∧ (g : Matrix (Fin 4) (Fin 4) K) 1 3 = 0 := by
  have key : ∀ {b c d : K}, h.bar b = b → h.bar d = d → ∀ j : Fin 4, j = 2 ∨ j = 3 →
      ∀ i, ((miyamotoX h 0 b c d) * (g : Matrix (Fin 4) (Fin 4) K)) i j =
        (g : Matrix (Fin 4) (Fin 4) K) i j := by
    intro b c d hb hd j hj i
    have hx : miyamotoXGL h 0 b c d ∈ miyamotoA1 h := (miyamotoXGL_mem_A1 h).2 ⟨rfl, hb, hd⟩
    obtain ⟨b', c', d', -, -, e⟩ := (mem_A1 h).1 ((mem_normalizer_iff''.1 hg _).1 hx)
    have e' : miyamotoXGL h 0 b c d * g = g * miyamotoXGL h 0 b' c' d' := by
      rw [← e]
      group
    have := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M i j) (congrArg Units.val e')
    simp only [Units.val_mul, coe_miyamotoXGL] at this
    rw [this]
    rcases hj with rfl | rfl <;> simp [Matrix.mul_apply, Fin.sum_univ_four, miyamotoX]
  have q02 := key (b := 0) (c := 0) (d := 1) (map_zero _) (map_one _) 2 (Or.inl rfl) 3
  have q03 := key (b := 0) (c := 0) (d := 1) (map_zero _) (map_one _) 3 (Or.inr rfl) 3
  have q12 := key (b := 1) (c := 0) (d := 0) (map_one _) (map_zero _) 2 (Or.inl rfl) 2
  have q13 := key (b := 1) (c := 0) (d := 0) (map_one _) (map_zero _) 3 (Or.inr rfl) 2
  simp [Matrix.mul_apply, Fin.sum_univ_four, miyamotoX] at q02 q03 q12 q13
  exact ⟨q02, q03, q12, q13⟩

end Shapes

end CFSG.LocalAnalysis.EvenBN.U4
