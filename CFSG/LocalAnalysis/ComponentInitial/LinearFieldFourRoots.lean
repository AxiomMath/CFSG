module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFieldFour

open Matrix LinearFlag
open scoped commutatorElement

section Field

variable {k : Type*} [Field k]

omit [Field k] in
theorem finite_of_card_eq_four (hk : Nat.card k = 4) : Finite k :=
  Nat.finite_of_card_ne_zero (by rw [hk]; norm_num)

theorem charP_two_of_card_eq_four (hk : Nat.card k = 4) : CharP k 2 :=
  finite_field_prime_power_characteristic Nat.prime_two (k := 2) (by norm_num)
    (by rw [hk]; norm_num)

theorem pow_three_eq_one (hk : Nat.card k = 4) {a : k} (ha : a ≠ 0) : a ^ 3 = 1 := by
  have := finite_of_card_eq_four hk
  have := Fintype.ofFinite k
  have h := FiniteField.pow_card_sub_one_eq_one a ha
  rwa [← Nat.card_eq_fintype_card, hk] at h

theorem pow_four_eq_self (hk : Nat.card k = 4) (a : k) : a ^ 4 = a := by
  have := finite_of_card_eq_four hk
  have := Fintype.ofFinite k
  have h := FiniteField.pow_card a
  rwa [← Nat.card_eq_fintype_card, hk] at h

theorem exists_ne_zero_ne_one (hk : Nat.card k = 4) : ∃ ω : k, ω ≠ 0 ∧ ω ≠ 1 := by
  classical
  have := finite_of_card_eq_four hk
  have := Fintype.ofFinite k
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hsub : (Finset.univ : Finset k) ⊆ {0, 1} := fun a _ => by
    by_cases ha : a = 0
    · simp [ha]
    · simp [h a ha]
  have hle := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hk] at hle
  have := Finset.card_le_two (a := (0 : k)) (b := 1)
  omega

variable {ω : k}

theorem omega_mul_omega (hk : Nat.card k = 4) (hω0 : ω ≠ 0) (hω1 : ω ≠ 1) :
    ω * ω = ω + 1 := by
  have := charP_two_of_card_eq_four hk
  have h3 := pow_three_eq_one hk hω0
  have h : (ω - 1) * (ω * ω + ω + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) hω1
  · linear_combination h - CharTwo.add_self_eq_zero (ω + 1)

theorem omega_cube (hk : Nat.card k = 4) (hω0 : ω ≠ 0) : ω * ω * ω = 1 := by
  rw [← pow_three_eq_one hk hω0]
  ring

theorem one_add_omega_add_omega_sq (hk : Nat.card k = 4) (hω0 : ω ≠ 0) (hω1 : ω ≠ 1) :
    1 + ω + ω * ω = 0 := by
  have := charP_two_of_card_eq_four hk
  rw [omega_mul_omega hk hω0 hω1]
  linear_combination CharTwo.add_self_eq_zero (1 + ω)

theorem eq_zero_or_eq_one_or (hk : Nat.card k = 4) (hω0 : ω ≠ 0) (hω1 : ω ≠ 1) (a : k) :
    a = 0 ∨ a = 1 ∨ a = ω ∨ a = ω + 1 := by
  classical
  have := finite_of_card_eq_four hk
  have := Fintype.ofFinite k
  have hc := charP_two_of_card_eq_four hk
  have h01 : (0 : k) ≠ 1 := zero_ne_one
  have h1 : ω + 1 ≠ 0 := fun h => hω1 (by linear_combination h - CharTwo.add_self_eq_zero (1 : k))
  have h2 : ω + 1 ≠ 1 := fun h => hω0 (by linear_combination h)
  have h3 : ω + 1 ≠ ω := fun h => h01 (by linear_combination -h)
  have hcard : ({0, 1, ω, ω + 1} : Finset k).card = Fintype.card k := by
    rw [← Nat.card_eq_fintype_card, hk, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_pair h3.symm]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hω1.symm, h2.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h01, hω0.symm, h1.symm⟩
  have ha := Finset.eq_univ_of_card _ hcard ▸ Finset.mem_univ a
  simpa only [Finset.mem_insert, Finset.mem_singleton] using ha

end Field

section Matrices

variable {k : Type*} [Field k]

@[expose] def xM (a : k) : Matrix (Fin 3) (Fin 3) k := !![1, a, 0; 0, 1, 0; 0, 0, 1]

@[expose] def yM (b : k) : Matrix (Fin 3) (Fin 3) k := !![1, 0, 0; 0, 1, b; 0, 0, 1]

@[expose] def wM (c : k) : Matrix (Fin 3) (Fin 3) k := !![1, 0, c; 0, 1, 0; 0, 0, 1]

@[expose] def hM (ω : k) : Matrix (Fin 3) (Fin 3) k := !![ω, 0, 0; 0, 1, 0; 0, 0, ω * ω]

@[expose] def s₂₃M : Matrix (Fin 3) (Fin 3) k := !![1, 0, 0; 0, 0, 1; 0, 1, 0]

@[expose] def s₁₂M : Matrix (Fin 3) (Fin 3) k := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

@[expose] def xMat (a : k) : SpecialLinearGroup (Fin 3) k := ⟨xM a, by simp [xM, det_fin_three]⟩

@[expose] def yMat (b : k) : SpecialLinearGroup (Fin 3) k := ⟨yM b, by simp [yM, det_fin_three]⟩

@[expose] def wMat (c : k) : SpecialLinearGroup (Fin 3) k := ⟨wM c, by simp [wM, det_fin_three]⟩

@[expose] def hMat (ω : k) (hω : ω * ω * ω = 1) : SpecialLinearGroup (Fin 3) k :=
  ⟨hM ω, by simp only [hM, det_fin_three]; simp; linear_combination hω⟩

@[expose] def s₂₃Mat [CharP k 2] : SpecialLinearGroup (Fin 3) k :=
  ⟨s₂₃M, by simp only [s₂₃M, det_fin_three]; simp [CharTwo.neg_eq]⟩

@[expose] def s₁₂Mat [CharP k 2] : SpecialLinearGroup (Fin 3) k :=
  ⟨s₁₂M, by simp only [s₁₂M, det_fin_three]; simp [CharTwo.neg_eq]⟩

theorem coe_wMat (c : k) : (wMat c : Matrix (Fin 3) (Fin 3) k) = wM c :=
  rfl

theorem xMat_add (a b : k) : xMat (a + b) = xMat a * xMat b := by
  apply Subtype.ext
  change xM (a + b) = xM a * xM b
  simp only [xM, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [add_comm]

theorem yMat_add (a b : k) : yMat (a + b) = yMat a * yMat b := by
  apply Subtype.ext
  change yM (a + b) = yM a * yM b
  simp only [yM, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [add_comm]

theorem wMat_add (a b : k) : wMat (a + b) = wMat a * wMat b := by
  apply Subtype.ext
  change wM (a + b) = wM a * wM b
  simp only [wM, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [add_comm]

theorem wMat_mul_xMat (c a : k) : wMat c * xMat a = xMat a * wMat c := by
  apply Subtype.ext
  change wM c * xM a = xM a * wM c
  simp only [wM, xM, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem wMat_mul_yMat (c b : k) : wMat c * yMat b = yMat b * wMat c := by
  apply Subtype.ext
  change wM c * yM b = yM b * wM c
  simp only [wM, yM, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem xMat_mul_yMat (a b : k) : xMat a * yMat b = wMat (a * b) * yMat b * xMat a := by
  apply Subtype.ext
  change xM a * yM b = wM (a * b) * yM b * xM a
  simp only [xM, yM, wM, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

variable {ω : k} (hω : ω * ω * ω = 1)

theorem hMat_mul_xMat (a : k) : hMat ω hω * xMat a = xMat (ω * a) * hMat ω hω := by
  apply Subtype.ext
  change hM ω * xM a = xM (ω * a) * hM ω
  simp only [hM, xM, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem hMat_mul_yMat (b : k) : hMat ω hω * yMat b = yMat (ω * b) * hMat ω hω := by
  apply Subtype.ext
  change hM ω * yM b = yM (ω * b) * hM ω
  simp only [hM, yM, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  linear_combination (-b) * hω

theorem hMat_mul_wMat (c : k) : hMat ω hω * wMat c = wMat (ω * ω * c) * hMat ω hω := by
  apply Subtype.ext
  change hM ω * wM c = wM (ω * ω * c) * hM ω
  simp only [hM, wM, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  linear_combination (-(ω * c)) * hω

variable [CharP k 2]

theorem s₂₃Mat_mul_self : (s₂₃Mat : SpecialLinearGroup (Fin 3) k) * s₂₃Mat = 1 := by
  apply Subtype.ext
  change (s₂₃M : Matrix (Fin 3) (Fin 3) k) * s₂₃M = 1
  simp only [s₂₃M, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem s₁₂Mat_mul_self : (s₁₂Mat : SpecialLinearGroup (Fin 3) k) * s₁₂Mat = 1 := by
  apply Subtype.ext
  change (s₁₂M : Matrix (Fin 3) (Fin 3) k) * s₁₂M = 1
  simp only [s₁₂M, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem s₂₃Mat_mul_xMat_mul_s₂₃Mat (a : k) : s₂₃Mat * xMat a * s₂₃Mat = wMat a := by
  apply Subtype.ext
  change s₂₃M * xM a * s₂₃M = wM a
  simp only [s₂₃M, xM, wM, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem s₁₂Mat_mul_yMat_mul_s₁₂Mat (b : k) : s₁₂Mat * yMat b * s₁₂Mat = wMat b := by
  apply Subtype.ext
  change s₁₂M * yM b * s₁₂M = wM b
  simp only [s₁₂M, yM, wM, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

omit [CharP k 2] in
theorem xMat_mem_scalars_iff (a : k) : xMat a ∈ scalars 3 k ↔ a = 0 := by
  constructor
  · rintro ⟨c, -, hc⟩
    have h := congrFun (congrFun hc 0) 1
    change xM a 0 1 = _ at h
    simpa [xM] using h
  · rintro rfl
    refine ⟨1, one_pow 3, ?_⟩
    change xM 0 = _
    simp only [xM, Units.val_one, map_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

omit [CharP k 2] in
theorem yMat_mem_scalars_iff (b : k) : yMat b ∈ scalars 3 k ↔ b = 0 := by
  constructor
  · rintro ⟨c, -, hc⟩
    have h := congrFun (congrFun hc 1) 2
    change yM b 1 2 = _ at h
    simpa [yM] using h
  · rintro rfl
    refine ⟨1, one_pow 3, ?_⟩
    change yM 0 = _
    simp only [yM, Units.val_one, map_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

omit [CharP k 2] in
theorem wMat_mem_scalars_iff (c : k) : wMat c ∈ scalars 3 k ↔ c = 0 := by
  constructor
  · rintro ⟨d, -, hd⟩
    have h := congrFun (congrFun hd 0) 2
    change wM c 0 2 = _ at h
    simpa [wM] using h
  · rintro rfl
    refine ⟨1, one_pow 3, ?_⟩
    change wM 0 = _
    simp only [wM, Units.val_one, map_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

end Matrices

section Projective

variable {k : Type*} [Field k]

@[expose] def xP (a : k) : projectiveSL 3 k := proj 3 k (xMat a)

@[expose] def yP (b : k) : projectiveSL 3 k := proj 3 k (yMat b)

@[expose] def wP (c : k) : projectiveSL 3 k := proj 3 k (wMat c)

@[expose] def hP (ω : k) (hω : ω * ω * ω = 1) : projectiveSL 3 k := proj 3 k (hMat ω hω)

@[expose] def s₂₃P [CharP k 2] : projectiveSL 3 k := proj 3 k s₂₃Mat

@[expose] def s₁₂P [CharP k 2] : projectiveSL 3 k := proj 3 k s₁₂Mat

theorem xP_add (a b : k) : xP (a + b) = xP a * xP b := by
  rw [xP, xMat_add, map_mul]
  rfl

theorem yP_add (a b : k) : yP (a + b) = yP a * yP b := by
  rw [yP, yMat_add, map_mul]
  rfl

theorem wP_add (a b : k) : wP (a + b) = wP a * wP b := by
  rw [wP, wMat_add, map_mul]
  rfl

theorem xP_eq_one_iff (a : k) : xP a = 1 ↔ a = 0 := by
  rw [xP, proj_eq_one_iff, xMat_mem_scalars_iff]

theorem yP_eq_one_iff (b : k) : yP b = 1 ↔ b = 0 := by
  rw [yP, proj_eq_one_iff, yMat_mem_scalars_iff]

theorem wP_eq_one_iff (c : k) : wP c = 1 ↔ c = 0 := by
  rw [wP, proj_eq_one_iff, wMat_mem_scalars_iff]

theorem wP_mul_xP (c a : k) : wP c * xP a = xP a * wP c := by
  rw [wP, xP, ← map_mul, ← map_mul, wMat_mul_xMat]

theorem wP_mul_yP (c b : k) : wP c * yP b = yP b * wP c := by
  rw [wP, yP, ← map_mul, ← map_mul, wMat_mul_yMat]

theorem commutatorElement_xP_yP (a b : k) : ⁅xP a, yP b⁆ = wP (a * b) := by
  have h : xP a * yP b = wP (a * b) * yP b * xP a := by
    rw [xP, yP, wP, ← map_mul, ← map_mul, ← map_mul, xMat_mul_yMat]
  rw [commutatorElement_def, h]
  group

variable {ω : k} (hω : ω * ω * ω = 1)

theorem hP_conj_xP (a : k) : hP ω hω * xP a * (hP ω hω)⁻¹ = xP (ω * a) := by
  rw [mul_inv_eq_iff_eq_mul, hP, xP, xP, ← map_mul, ← map_mul, hMat_mul_xMat]

theorem hP_conj_yP (b : k) : hP ω hω * yP b * (hP ω hω)⁻¹ = yP (ω * b) := by
  rw [mul_inv_eq_iff_eq_mul, hP, yP, yP, ← map_mul, ← map_mul, hMat_mul_yMat]

theorem hP_conj_wP (c : k) : hP ω hω * wP c * (hP ω hω)⁻¹ = wP (ω * ω * c) := by
  rw [mul_inv_eq_iff_eq_mul, hP, wP, wP, ← map_mul, ← map_mul, hMat_mul_wMat]

variable [CharP k 2]

theorem s₂₃P_inv : (s₂₃P : projectiveSL 3 k)⁻¹ = s₂₃P := by
  rw [inv_eq_iff_mul_eq_one, s₂₃P, ← map_mul, s₂₃Mat_mul_self, map_one]

theorem s₁₂P_inv : (s₁₂P : projectiveSL 3 k)⁻¹ = s₁₂P := by
  rw [inv_eq_iff_mul_eq_one, s₁₂P, ← map_mul, s₁₂Mat_mul_self, map_one]

theorem s₂₃P_conj_xP (a : k) : (s₂₃P : projectiveSL 3 k)⁻¹ * xP a * s₂₃P = wP a := by
  rw [s₂₃P_inv, s₂₃P, xP, wP, ← map_mul, ← map_mul, s₂₃Mat_mul_xMat_mul_s₂₃Mat]

theorem s₁₂P_conj_yP (b : k) : (s₁₂P : projectiveSL 3 k)⁻¹ * yP b * s₁₂P = wP b := by
  rw [s₁₂P_inv, s₁₂P, yP, wP, ← map_mul, ← map_mul, s₁₂Mat_mul_yMat_mul_s₁₂Mat]

end Projective

end LinearFieldFour

end CFSG.LocalAnalysis.ComponentInitial
