module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Klein

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open Matrix CFSG.Open

section Matrices

variable {K : Type} [Field K] {ζ : K}

@[expose] def uD1 : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

@[expose] def uD2 (ζ : K) : Matrix (Fin 3) (Fin 3) K := !![ζ, ζ ^ 2, 0; ζ ^ 2, ζ, 0; 0, 0, 1]

@[expose] def uC (ζ : K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, ζ, ζ ^ 2; ζ ^ 2, 1, ζ ^ 2; ζ, ζ, 1]

theorem uD1_mul_self : (uD1 : Matrix (Fin 3) (Fin 3) K) * uD1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uD1, Matrix.mul_apply, Fin.sum_univ_three]

theorem uD1_comm : (uD1 : Matrix (Fin 3) (Fin 3) K) * uD2 ζ = uD2 ζ * uD1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uD1, uD2, Matrix.mul_apply, Fin.sum_univ_three]

theorem uD1_transpose : (uD1 : Matrix (Fin 3) (Fin 3) K)ᵀ = uD1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uD1]

theorem uD2_transpose : (uD2 ζ)ᵀ = uD2 ζ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uD2]

theorem uD2_mul_self (h2 : (2 : K) = 0) (hz : ζ ^ 2 + ζ + 1 = 0) :
    uD2 ζ * uD2 ζ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [uD2, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((1) + (-1) * ζ + (1) * ζ ^ 2) * hz + ((-1)) * h2
  · simp [uD2, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((-2) + (2) * ζ) * hz + ((1)) * h2
  · simp [uD2, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [uD2, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((-2) + (2) * ζ) * hz + ((1)) * h2
  · simp [uD2, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((1) + (-1) * ζ + (1) * ζ ^ 2) * hz + ((-1)) * h2
  · simp [uD2, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [uD2, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [uD2, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [uD2, Matrix.mul_apply, Fin.sum_univ_three]

theorem uC_cubed (h2 : (2 : K) = 0) (hz : ζ ^ 2 + ζ + 1 = 0) :
    uC ζ * uC ζ * uC ζ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [uC, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((-1) + (1) * ζ + (1) * ζ ^ 3) * hz + (0) * h2
  · simp [uC, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((-2) + (-1) * ζ + (3) * ζ ^ 2) * hz + ((1) + (2) * ζ) * h2
  · simp [uC, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((2) + (2) * ζ + (-3) * ζ ^ 2 + (3) * ζ ^ 3) * hz + ((-1) + (-2) * ζ) * h2
  · simp [uC, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((2) + (2) * ζ + (-3) * ζ ^ 2 + (3) * ζ ^ 3) * hz + ((-1) + (-2) * ζ) * h2
  · simp [uC, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((-4) + (4) * ζ + (1) * ζ ^ 3) * hz + ((2)) * h2
  · simp [uC, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((6) + (-2) * ζ + (-1) * ζ ^ 2 + (3) * ζ ^ 3) * hz + ((-3) + (-2) * ζ) * h2
  · simp [uC, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((-2) + (-1) * ζ + (3) * ζ ^ 2) * hz + ((1) + (2) * ζ) * h2
  · simp [uC, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((2) + (-3) * ζ + (3) * ζ ^ 2) * hz + ((-1) + (2) * ζ) * h2
  · simp [uC, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((-4) + (4) * ζ + (1) * ζ ^ 3) * hz + ((2)) * h2

theorem uC_conj1 (h2 : (2 : K) = 0) (hz : ζ ^ 2 + ζ + 1 = 0) :
    uC ζ * uD1 * (uC ζ * uC ζ) = uD2 ζ := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [uC, uD1, uD2, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((-1) * ζ + (1) * ζ ^ 2 + (1) * ζ ^ 3) * hz + (0) * h2
  · simp [uC, uD1, uD2, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((-2) + (2) * ζ ^ 2) * hz + ((1) + (1) * ζ) * h2
  · simp [uC, uD1, uD2, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((2) + (-1) * ζ ^ 2 + (2) * ζ ^ 3) * hz + ((-1) + (-1) * ζ) * h2
  · simp [uC, uD1, uD2, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((-2) + (2) * ζ + (-1) * ζ ^ 2 + (2) * ζ ^ 3) * hz + ((1)) * h2
  · simp [uC, uD1, uD2, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((2) * ζ + (-1) * ζ ^ 2 + (2) * ζ ^ 3) * hz + ((-1) * ζ) * h2
  · simp [uC, uD1, uD2, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((2) + (1) * ζ ^ 3 + (1) * ζ ^ 4) * hz + ((-1) + (-1) * ζ) * h2
  · simp [uC, uD1, uD2, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((-2) + (-1) * ζ + (3) * ζ ^ 2) * hz + ((1) + (2) * ζ) * h2
  · simp [uC, uD1, uD2, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((2) + (-3) * ζ + (3) * ζ ^ 2) * hz + ((-1) + (2) * ζ) * h2
  · simp [uC, uD1, uD2, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((-4) + (4) * ζ + (1) * ζ ^ 3) * hz + ((2)) * h2

theorem uC_conj2 (h2 : (2 : K) = 0) (hz : ζ ^ 2 + ζ + 1 = 0) :
    uC ζ * uD2 ζ * (uC ζ * uC ζ) = uD1 * uD2 ζ := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [uC, uD1, uD2, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((-2) + (2) * ζ + (-1) * ζ ^ 2 + (2) * ζ ^ 4) * hz + ((1)) * h2
  · simp [uC, uD1, uD2, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((1) * ζ + (1) * ζ ^ 3 + (1) * ζ ^ 4) * hz + ((-1) * ζ) * h2
  · simp [uC, uD1, uD2, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((2) + (-1) * ζ ^ 2 + (1) * ζ ^ 3 + (2) * ζ ^ 4) * hz + ((-1) +
      (-1) * ζ) * h2
  · simp [uC, uD1, uD2, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((-2) + (3) * ζ + (-1) * ζ ^ 2 + (2) * ζ ^ 4 + (1) * ζ ^ 5) * hz + ((1) +
      (-1) * ζ) * h2
  · simp [uC, uD1, uD2, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((-4) + (-3) * ζ + (6) * ζ ^ 2 + (-1) * ζ ^ 4 + (2) * ζ ^ 5) * hz + ((2) +
      (4) * ζ) * h2
  · simp [uC, uD1, uD2, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((2) + (4) * ζ + (-5) * ζ ^ 2 + (3) * ζ ^ 3 + (3) * ζ ^ 4 + (-1) * ζ ^ 5 +
      (1) * ζ ^ 6) * hz + ((-1) + (-3) * ζ) * h2
  · simp [uC, uD1, uD2, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((3) * ζ + (-3) * ζ ^ 2 + (1) * ζ ^ 3 + (3) * ζ ^ 4) * hz + ((-1) * ζ) * h2
  · simp [uC, uD1, uD2, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((4) * ζ + (-2) * ζ ^ 2 + (3) * ζ ^ 4) * hz + ((-1) * ζ) * h2
  · simp [uC, uD1, uD2, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((2) * ζ ^ 3 + (1) * ζ ^ 4 + (1) * ζ ^ 5) * hz + (0) * h2

theorem uC_orth (h2 : (2 : K) = 0) (hz : ζ ^ 2 + ζ + 1 = 0) :
    (uC ζ)ᵀ * uC ζ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [uC, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((1) + (-1) * ζ + (1) * ζ ^ 2) * hz + ((-1)) * h2
  · simp [uC, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((2)) * hz + ((-1) + (-1) * ζ) * h2
  · simp [uC, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((-1) * ζ + (1) * ζ ^ 2) * hz + ((1) * ζ) * h2
  · simp [uC, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((2)) * hz + ((-1) + (-1) * ζ) * h2
  · simp [uC, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((2)) * hz + ((-1) + (-1) * ζ) * h2
  · simp [uC, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((1) * ζ) * hz + (0) * h2
  · simp [uC, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((-1) * ζ + (1) * ζ ^ 2) * hz + ((1) * ζ) * h2
  · simp [uC, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((1) * ζ) * hz + (0) * h2
  · simp [uC, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination ((-2) * ζ + (2) * ζ ^ 2) * hz + ((1) * ζ) * h2

theorem det_uD1 (h2 : (2 : K) = 0) (hz : ζ ^ 2 + ζ + 1 = 0) :
    ((uD1 : Matrix (Fin 3) (Fin 3) K)).det = 1 := by
  simp [uD1, det_fin_three]
  linear_combination (0) * hz + ((-1)) * h2

theorem det_uD2 (h2 : (2 : K) = 0) (hz : ζ ^ 2 + ζ + 1 = 0) :
    (uD2 ζ).det = 1 := by
  simp [uD2, det_fin_three]
  linear_combination ((1) + (1) * ζ + (-1) * ζ ^ 2) * hz + ((-1) + (-1) * ζ) * h2

theorem det_uC (h2 : (2 : K) = 0) (hz : ζ ^ 2 + ζ + 1 = 0) :
    (uC ζ).det = 1 := by
  simp [uC, det_fin_three]
  linear_combination ((3) + (-3) * ζ + (1) * ζ ^ 3) * hz + ((-2)) * h2

@[expose] def glU2 (h2 : (2 : K) = 0) (hz : ζ ^ 2 + ζ + 1 = 0) : GL (Fin 3) K :=
  ⟨uD2 ζ, uD2 ζ, uD2_mul_self h2 hz, uD2_mul_self h2 hz⟩

@[expose] def glU1 : GL (Fin 3) K := ⟨uD1, uD1, uD1_mul_self, uD1_mul_self⟩

@[expose] def glUC (h2 : (2 : K) = 0) (hz : ζ ^ 2 + ζ + 1 = 0) : GL (Fin 3) K :=
  ⟨uC ζ, uC ζ * uC ζ, by rw [← mul_assoc]; exact uC_cubed h2 hz, uC_cubed h2 hz⟩

end Matrices

section Main

variable {K : Type} [Field K] {ζ : K} {q : ℕ}

theorem map_fix (hfix : ζ ^ q = ζ) (hq : q ≠ 0) :
    (uD1 : Matrix (Fin 3) (Fin 3) K).map (· ^ q) = uD1 ∧ (uD2 ζ).map (· ^ q) = uD2 ζ ∧
      (uC ζ).map (· ^ q) = uC ζ := by
  have h1 : (ζ ^ 2) ^ q = ζ ^ 2 := by rw [← pow_mul, mul_comm, pow_mul, hfix]
  have h0 : (0 : K) ^ q = 0 := zero_pow hq
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [uD1, uD2, uC, hfix, h1, h0]

theorem glU1_mem_su (h2 : (2 : K) = 0) (hz : ζ ^ 2 + ζ + 1 = 0) (hfix : ζ ^ q = ζ) (hq : q ≠ 0) :
    (glU1 : GL (Fin 3) K) ∈ StatedSU 3 q K := by
  refine Subgroup.subset_closure ⟨det_uD1 h2 hz, ?_⟩
  show ((uD1 : Matrix (Fin 3) (Fin 3) K).map (· ^ q))ᵀ * uD1 = 1
  rw [(map_fix hfix hq).1, uD1_transpose]
  exact uD1_mul_self

theorem glU2_mem_su (h2 : (2 : K) = 0) (hz : ζ ^ 2 + ζ + 1 = 0) (hfix : ζ ^ q = ζ) (hq : q ≠ 0) :
    (glU2 h2 hz : GL (Fin 3) K) ∈ StatedSU 3 q K := by
  refine Subgroup.subset_closure ⟨det_uD2 h2 hz, ?_⟩
  show ((uD2 ζ).map (· ^ q))ᵀ * uD2 ζ = 1
  rw [(map_fix hfix hq).2.1, uD2_transpose]
  exact uD2_mul_self h2 hz

theorem glUC_mem_su (h2 : (2 : K) = 0) (hz : ζ ^ 2 + ζ + 1 = 0) (hfix : ζ ^ q = ζ) (hq : q ≠ 0) :
    (glUC h2 hz : GL (Fin 3) K) ∈ StatedSU 3 q K := by
  refine Subgroup.subset_closure ⟨det_uC h2 hz, ?_⟩
  show ((uC ζ).map (· ^ q))ᵀ * uC ζ = 1
  rw [(map_fix hfix hq).2.2]
  exact uC_orth h2 hz

theorem threeTwoWitness_psu_three_of_cube [Finite K] (h2 : (2 : K) = 0)
    (hz : ζ ^ 2 + ζ + 1 = 0) (hfix : ζ ^ q = ζ) (hq : q ≠ 0) :
    ThreeTwoWitness (StatedProj (StatedSU 3 q K)) := by
  refine threeTwoWitness_statedProj_klein glU1 (glU2 h2 hz) (glUC h2 hz)
    (glU1_mem_su h2 hz hfix hq) (glU2_mem_su h2 hz hfix hq) (glUC_mem_su h2 hz hfix hq)
    (Units.ext uD1_mul_self) (Units.ext (uD2_mul_self h2 hz)) (Units.ext uD1_comm) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    have e := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 1) hu
    simp [glU1, uD1, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at e
  · refine Units.ext ?_
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    show uC ζ ^ 3 = 1
    rw [pow_succ, pow_two]
    exact uC_cubed h2 hz
  · intro u hu
    have e := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) hu
    simp [glUC, uC, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at e
  · exact Units.ext (uC_conj1 h2 hz)
  · exact Units.ext (uC_conj2 h2 hz)

end Main


theorem threeTwoWitness_psu_three_two_pow_even {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : Even f) :
    ThreeTwoWitness (StatedProj (StatedSU 3 (2 ^ f) K)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have hc : CharP K 2 := charP_of_card_eq_prime_pow (f := 2 * f) (by
    rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm])
  have h2 : (2 : K) = 0 := by simpa using CharP.cast_eq_zero K 2
  have e : (2 ^ f) ^ 2 = (2 ^ 2) ^ f := by rw [← pow_mul, ← pow_mul, mul_comm]
  have h3 : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK, e]
    have := Nat.sub_dvd_pow_sub_pow (2 ^ 2) 1 f
    rw [one_pow] at this
    exact this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hg3 : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hz3 : ((g : Kˣ) : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hg3, Units.val_one]
  have hz1 : ((g : Kˣ) : K) ≠ 1 := by
    intro h
    have : g = 1 := Units.ext (by simpa using h)
    rw [this, orderOf_one] at hg
    norm_num at hg
  have hz0 : ((g : Kˣ) : K) ≠ 0 := g.ne_zero
  have hz : ((g : Kˣ) : K) ^ 2 + ((g : Kˣ) : K) + 1 = 0 := by
    have h : (((g : Kˣ) : K) - 1) * (((g : Kˣ) : K) ^ 2 + ((g : Kˣ) : K) + 1) = 0 := by
      linear_combination hz3
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hz1)
  have hmod : 2 ^ f % 3 = 1 := by
    obtain ⟨m, hm⟩ := hf
    rw [hm, ← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  have hfix : ((g : Kˣ) : K) ^ (2 ^ f) = ((g : Kˣ) : K) := by
    have hd : 2 ^ f = 3 * (2 ^ f / 3) + 1 := by omega
    rw [hd, pow_succ, pow_mul, hz3, one_pow, one_mul]
  exact threeTwoWitness_psu_three_of_cube h2 hz hfix (by positivity)

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
