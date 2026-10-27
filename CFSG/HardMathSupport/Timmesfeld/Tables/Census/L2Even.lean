module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Klein

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open Matrix CFSG.Open

variable {K : Type} [Field K]

@[expose] def mU (x : K) : Matrix (Fin 2) (Fin 2) K := !![1, x; 0, 1]

theorem mU_mul (x y : K) : mU x * mU y = mU (x + y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mU, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem mU_zero : mU (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mU]

@[expose] def glU (x : K) : GL (Fin 2) K :=
  ⟨mU x, mU (-x), by rw [mU_mul, add_neg_cancel, mU_zero], by rw [mU_mul, neg_add_cancel, mU_zero]⟩

theorem det_mU (x : K) : (mU x).det = 1 := by simp [mU, det_fin_two]

theorem glU_mem (x : K) : glU x ∈ StatedSL 2 K := Subgroup.subset_closure (det_mU x)

section Cube

variable {ζ : K} (hz3 : ζ ^ 3 = 1)

@[expose] def mCe (ζ : K) : Matrix (Fin 2) (Fin 2) K := !![ζ ^ 2, 0; 0, ζ]

@[expose] def mCei (ζ : K) : Matrix (Fin 2) (Fin 2) K := !![ζ, 0; 0, ζ ^ 2]

include hz3 in
theorem mCe_mul_mCei : mCe ζ * mCei ζ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mCe, mCei, Matrix.mul_apply, Fin.sum_univ_two] <;>
    linear_combination hz3

include hz3 in
theorem mCei_mul_mCe : mCei ζ * mCe ζ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mCe, mCei, Matrix.mul_apply, Fin.sum_univ_two] <;>
    linear_combination hz3

include hz3 in
theorem mCe_mU_mCei (x : K) : mCe ζ * mU x * mCei ζ = mU (ζ * x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mCe, mCei, mU, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination hz3 | linear_combination (-(ζ * x)) * hz3 |
      linear_combination (ζ * x) * hz3

@[expose] def glCe (hz3 : ζ ^ 3 = 1) : GL (Fin 2) K :=
  ⟨mCe ζ, mCei ζ, mCe_mul_mCei hz3, mCei_mul_mCe hz3⟩

theorem det_mCe (hz3 : ζ ^ 3 = 1) : (mCe ζ).det = 1 := by
  simp [mCe, det_fin_two]
  linear_combination hz3

theorem glCe_mem (hz3 : ζ ^ 3 = 1) : glCe hz3 ∈ StatedSL 2 K :=
  Subgroup.subset_closure (det_mCe hz3)

theorem glCe_conj (hz3 : ζ ^ 3 = 1) (x : K) : glCe hz3 * glU x * (glCe hz3)⁻¹ = glU (ζ * x) :=
  Units.ext (mCe_mU_mCei hz3 x)

end Cube

theorem glU_mul (x y : K) : glU x * glU y = glU (x + y) := Units.ext (mU_mul x y)

theorem glU_zero : glU (0 : K) = 1 := Units.ext mU_zero

theorem threeTwoWitness_psl_two_of_cube [Finite K] (h2 : (1 : K) + 1 = 0) {ζ : K}
    (hz3 : ζ ^ 3 = 1) (hz1 : ζ ≠ 1) : ThreeTwoWitness (StatedProj (StatedSL 2 K)) := by
  have hz0 : ζ ≠ 0 := fun h => by simp [h] at hz3
  have hq : ζ ^ 2 = 1 + ζ := by
    have h : (ζ - 1) * (ζ ^ 2 + ζ + 1) = 0 := by linear_combination hz3
    have := (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hz1)
    linear_combination this - (ζ + 1) * h2
  have h2' : ∀ x : K, x + x = 0 := fun x => by linear_combination x * h2
  refine threeTwoWitness_statedProj_klein (glU 1) (glU ζ) (glCe hz3) (glU_mem 1) (glU_mem ζ)
    (glCe_mem hz3) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [glU_mul, h2, glU_zero]
  · rw [glU_mul, h2' ζ, glU_zero]
  · rw [glU_mul, glU_mul, add_comm]
  · intro u hu
    have e := congrArg (fun A : GL (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 0 1) hu
    simp [glU, mU, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at e
  · refine Units.ext ?_
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    show mCe ζ ^ 3 = 1
    rw [pow_succ, pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mCe, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination hz3 | linear_combination (ζ ^ 3 + 1) * hz3
  · intro u hu
    have e0 := congrArg (fun A : GL (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) hu
    have e1 := congrArg (fun A : GL (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 1 1) hu
    simp [glCe, mCe, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at e0 e1
    exact hz1 (mul_left_cancel₀ hz0 (by linear_combination e1.symm.trans e0 |>.symm))
  · rw [glCe_conj hz3, mul_one]
  · rw [glCe_conj hz3, glU_mul, ← pow_two, hq]

theorem threeTwoWitness_psl_two_pow_even {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : Even f) :
    ThreeTwoWitness (StatedProj (StatedSL 2 K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  classical
  have : Fintype K := Fintype.ofFinite K
  have hc : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK])
  have h2 : (1 : K) + 1 = 0 := by
    have : ((2 : ℕ) : K) = 0 := CharP.cast_eq_zero K 2
    simpa [one_add_one_eq_two] using this
  obtain ⟨m, hm⟩ := hf
  have h3 : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK,
      show f = 2 * m by omega, pow_mul]
    have := Nat.sub_dvd_pow_sub_pow (2 ^ 2) 1 m
    rw [one_pow] at this
    exact this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 h3
  refine threeTwoWitness_psl_two_of_cube h2 (ζ := (g : K)) ?_ ?_
  · rw [← Units.val_pow_eq_pow_val, ← hg, pow_orderOf_eq_one, Units.val_one]
  · intro h
    have : g = 1 := Units.ext (by simpa using h)
    rw [this, orderOf_one] at hg
    norm_num at hg

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
