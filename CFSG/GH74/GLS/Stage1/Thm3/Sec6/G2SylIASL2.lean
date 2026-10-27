module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.G2Syl

open scoped MatrixGroups
open Subgroup

namespace IASL2

section Trace

variable {F : Type*} [Field F]

theorem trace_mul_self (B : SL(2, F)) :
    ((B * B : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace =
      ((B : Matrix (Fin 2) (Fin 2) F).trace) ^ 2 - 2 := by
  have hdet := B.det_coe
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two]
  linear_combination (-2) * hdet

theorem trace_pow_two_pow (h2 : (2 : F) = 0) (A : SL(2, F)) (j : ℕ) :
    ((A ^ (2 ^ j) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).trace =
      ((A : Matrix (Fin 2) (Fin 2) F).trace) ^ (2 ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_mul, sq, trace_mul_self, ih, h2, sub_zero, ← pow_mul, ← pow_succ]

theorem mul_self_eq_one_of_trace_eq_zero (h2 : (2 : F) = 0) (A : SL(2, F))
    (ht : (A : Matrix (Fin 2) (Fin 2) F).trace = 0) : A * A = 1 := by
  have hdet := A.det_coe
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two] at ht
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (-1) * hdet + (A : Matrix (Fin 2) (Fin 2) F) 0 0 * ht - h2
  · linear_combination (A : Matrix (Fin 2) (Fin 2) F) 0 1 * ht
  · linear_combination (A : Matrix (Fin 2) (Fin 2) F) 1 0 * ht
  · linear_combination (-1) * hdet + (A : Matrix (Fin 2) (Fin 2) F) 1 1 * ht - h2

end Trace

section Card

variable {F : Type*} [Field F] [Finite F]

theorem natCard_mod_two_of_two_ne_zero (h2 : (2 : F) ≠ 0) : Nat.card F % 2 = 1 := by
  have := Fintype.ofFinite F
  have hne : ringChar F ≠ 2 := by
    intro h
    apply h2
    have := ringChar.Nat.cast_ringChar (R := F)
    rwa [h, Nat.cast_ofNat] at this
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.odd_card_of_char_ne_two hne

theorem natCard_sl2 : Nat.card SL(2, F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  let := Fintype.ofFinite F
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card F ^ 2 - Fintype.card F =
      Fintype.card F * (Fintype.card F - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

end Card

section Quaternion

variable {F : Type*} [Field F] [Finite F]

theorem exists_sq_add_sq_eq_neg_one (h2 : (2 : F) ≠ 0) : ∃ x y : F, x ^ 2 + y ^ 2 = -1 := by
  have := Fintype.ofFinite F
  have hodd : Fintype.card F % 2 = 1 := by
    have := natCard_mod_two_of_two_ne_zero h2
    rwa [Nat.card_eq_fintype_card] at this
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (R := F)
    (f := Polynomial.X ^ 2) (g := Polynomial.X ^ 2 + Polynomial.C 1)
    (Polynomial.degree_X_pow 2) (Polynomial.degree_X_pow_add_C (by norm_num) 1) hodd
  refine ⟨a, b, ?_⟩
  simp at hab
  linear_combination hab

theorem exists_quaternion_pair (h2 : (2 : F) ≠ 0) :
    ∃ I J : SL(2, F), I ^ 4 = 1 ∧ J ^ 4 = 1 ∧ J * I * J⁻¹ = I⁻¹ ∧ I * J ≠ J * I := by
  obtain ⟨x, y, hxy⟩ := exists_sq_add_sq_eq_neg_one h2
  have hdI : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    simp [Matrix.det_fin_two]
  have hdJ : (!![x, y; y, -x] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination (-1) * hxy
  obtain ⟨I, hI⟩ : ∃ I : SL(2, F), (I : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] :=
    ⟨⟨_, hdI⟩, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J : SL(2, F), (J : Matrix (Fin 2) (Fin 2) F) = !![x, y; y, -x] :=
    ⟨⟨_, hdJ⟩, rfl⟩
  have hI4 : I ^ 4 = 1 := by
    apply Subtype.ext
    simp [hI, pow_succ, Matrix.one_fin_two]
  have hJJ : J * J = I * I := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, hI, hJ, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> first | ring1 | linear_combination hxy
  have hJ4 : J ^ 4 = 1 := by
    calc J ^ 4 = (J * J) * (J * J) := by simp [pow_succ, mul_assoc]
      _ = (I * I) * (I * I) := by rw [hJJ]
      _ = I ^ 4 := by simp [pow_succ, mul_assoc]
      _ = 1 := hI4
  have hIinv : I⁻¹ = I * I * I := by
    apply inv_eq_of_mul_eq_one_right
    calc I * (I * I * I) = I ^ 4 := by simp [pow_succ, mul_assoc]
      _ = 1 := hI4
  have hJIc : J * I * J⁻¹ = I⁻¹ := by
    rw [mul_inv_eq_iff_eq_mul, hIinv]
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, hI, hJ, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  refine ⟨I, J, hI4, hJ4, hJIc, ?_⟩
  intro h
  have h00 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  have h01 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [hI, hJ] at h00 h01
  have hy : y = 0 :=
    (mul_eq_zero.1 (show (2 : F) * y = 0 by linear_combination (-1) * h00)).resolve_left h2
  have hx : x = 0 :=
    (mul_eq_zero.1 (show (2 : F) * x = 0 by linear_combination h01)).resolve_left h2
  rw [hx, hy] at hxy
  exact one_ne_zero (show (1 : F) = 0 by linear_combination hxy)

end Quaternion

section Group

variable {G : Type*} [Group G]

theorem isPGroup_zpowers_two {a : G} {k : ℕ} (h : a ^ (2 ^ k) = 1) :
    IsPGroup 2 (zpowers a) :=
  IsPGroup.of_card_dvd_pow (n := k) (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one h)

theorem isPGroup_sup_zpowers {I J : G} (hI : I ^ 4 = 1) (hJ : J ^ 4 = 1)
    (hJI : J * I * J⁻¹ = I⁻¹) : IsPGroup 2 (zpowers I ⊔ zpowers J : Subgroup G) := by
  have h1 : J * I⁻¹ * J⁻¹ = I := by
    have := congrArg (·⁻¹) hJI
    simpa [mul_assoc] using this
  have hJI' : J⁻¹ * I * J = I⁻¹ := by
    calc J⁻¹ * I * J = J⁻¹ * (J * I⁻¹ * J⁻¹) * J := by rw [h1]
      _ = I⁻¹ := by group
  refine (isPGroup_zpowers_two (k := 2) (by simpa using hI)).to_sup_of_normal_left'
    (isPGroup_zpowers_two (k := 2) (by simpa using hJ)) ?_
  rw [zpowers_le, mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨-n, ?_⟩
    show I ^ (-n) = J * I ^ n * J⁻¹
    rw [← conj_zpow, hJI, zpow_neg, inv_zpow]
  · rintro ⟨n, hn⟩
    have hn' : I ^ n = J * h * J⁻¹ := hn
    have : h = J⁻¹ * (J * h * J⁻¹) * J := by group
    rw [this, ← hn']
    refine ⟨-n, ?_⟩
    have hc := conj_zpow (a := J⁻¹) (b := I) (i := n)
    rw [inv_inv, hJI'] at hc
    show I ^ (-n) = J⁻¹ * I ^ n * J
    rw [← hc, zpow_neg, inv_zpow]

theorem exists_noncomm_mem_sylow [Finite G] (T : Sylow 2 G) {I J : G}
    (hP : IsPGroup 2 (zpowers I ⊔ zpowers J : Subgroup G)) (hIJ : I * J ≠ J * I) :
    ∃ a ∈ (T : Subgroup G), ∃ b ∈ (T : Subgroup G), a * b ≠ b * a := by
  obtain ⟨P, hP'⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P T
  have hmem : ∀ x ∈ (zpowers I ⊔ zpowers J : Subgroup G), g * x * g⁻¹ ∈ (T : Subgroup G) := by
    intro x hx
    rw [← hg, Sylow.coe_subgroup_smul]
    have := Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (P : Subgroup G) (hP' hx)
    simpa using this
  refine ⟨g * I * g⁻¹, hmem I (mem_sup_left (mem_zpowers I)), g * J * g⁻¹,
    hmem J (mem_sup_right (mem_zpowers J)), ?_⟩
  intro h
  apply hIJ
  have h' : g * (I * J) * g⁻¹ = g * (J * I) * g⁻¹ := by
    calc g * (I * J) * g⁻¹ = (g * I * g⁻¹) * (g * J * g⁻¹) := by group
      _ = (g * J * g⁻¹) * (g * I * g⁻¹) := h
      _ = g * (J * I) * g⁻¹ := by group
  simpa using h'

end Group

end IASL2

open IASL2

theorem sl2_sq_eq_one_of_char_two {F : Type*} [Field F] (h2 : (2 : F) = 0)
    (A : Matrix.SpecialLinearGroup (Fin 2) F) {j : ℕ} (hA : A ^ (2 ^ j) = 1) : A * A = 1 := by
  apply mul_self_eq_one_of_trace_eq_zero h2
  have h1 := trace_pow_two_pow h2 A j
  rw [hA] at h1
  simp at h1
  rw [h2] at h1
  exact (pow_eq_zero_iff (by positivity)).1 h1.symm

theorem sl2_sylow_card {F : Type*} [Field F] [Finite F] (h2 : (2 : F) ≠ 0)
    (T : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F)) :
    Nat.card ↥(T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) =
      2 ^ ((Nat.card F ^ 2 - 1).factorization 2) := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hq2 : 1 < Nat.card F ^ 2 := Nat.one_lt_pow two_ne_zero hq
  rw [Sylow.card_eq_multiplicity, natCard_sl2, Nat.factorization_mul (by omega) (by omega),
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd, zero_add]
  have := natCard_mod_two_of_two_ne_zero h2
  omega

theorem sl2_sylow_noncomm {F : Type*} [Field F] [Finite F] (h2 : (2 : F) ≠ 0)
    (T : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F)) :
    ∃ a ∈ (T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)),
      ∃ b ∈ (T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)), a * b ≠ b * a := by
  obtain ⟨I, J, hI, hJ, hJI, hIJ⟩ := exists_quaternion_pair h2
  exact exists_noncomm_mem_sylow T (isPGroup_sup_zpowers hI hJ hJI) hIJ

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.G2Syl
