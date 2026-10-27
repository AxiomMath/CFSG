module

public import CFSG.CGT.Stroth77.Section34T201Mats
public import CFSG.CGT.Stroth77.Section34T201Natural

public section

namespace CFSG.CGT.Stroth77

namespace Stroth34T201Ident

open Matrix Stroth34T201Levels Stroth34T201Natural

section

attribute [local simp] Type201.k Type201.ρM Type201.uvA Type201.tM Type201.uvM Type201.uM
  Type200.k Type200.ρM Type200.uvA Type200.tM Type200.uvM Type200.uM uMat eMat conjρ conjU
  theta₁₁ theta₁₂ theta₂₁ theta₂₂ ofCols_apply Matrix.mul_apply Fin.sum_univ_three Matrix.mulVec
  dotProduct Matrix.one_apply

theorem conjρ_theta₁₁ {m : ℕ} (hm : 2 ≤ m) :
    MatEq (Type201.k m) (conjρ (theta₁₁ m)) (theta₁₂ m * eMat m) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  refine MatEq.of_witness (W := !![-2, 5, -4 * 2 ^ j - 2; -1, 1, -4 * 2 ^ j - 1;
    0, 0, -4 * 2 ^ j - 1]) fun i l => ?_
  fin_cases i <;> fin_cases l <;>
    simp [show j + 2 - 1 = j + 1 from rfl, -mul_eq_zero, -mul_eq_mul_left_iff,
      -mul_eq_mul_right_iff] <;> ring1

theorem conjρ_theta₂₁ {m : ℕ} (hm : 2 ≤ m) :
    MatEq (Type201.k m) (conjρ (theta₂₁ m)) (theta₂₂ m * eMat m) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  refine MatEq.of_witness (W := !![-2, 1, -4 * 2 ^ j; -1, 0, 0; 0, 0, -4 * 2 ^ j - 1])
    fun i l => ?_
  fin_cases i <;> fin_cases l <;>
    simp [show j + 2 - 1 = j + 1 from rfl, -mul_eq_zero, -mul_eq_mul_left_iff,
      -mul_eq_mul_right_iff] <;> ring1

theorem theta₁₁_mul_self {m : ℕ} (hm : 2 ≤ m) :
    MatEq (Type201.k m) (theta₁₁ m * theta₁₁ m) 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  refine MatEq.of_witness (W := !![8 * 2 ^ j, 8 * 2 ^ j + 1, 8 * 2 ^ j + 1;
    8 * 2 ^ j + 1, 9 * 2 ^ j + 1, 9 * 2 ^ j + 1; 8 * 2 ^ j + 1, 9 * 2 ^ j + 1, 9 * 2 ^ j + 1])
    fun i l => ?_
  fin_cases i <;> fin_cases l <;>
    simp [show j + 2 - 1 = j + 1 from rfl, -mul_eq_zero, -mul_eq_mul_left_iff,
      -mul_eq_mul_right_iff] <;> ring1

theorem theta₂₁_mul_self {m : ℕ} (hm : 2 ≤ m) :
    MatEq (Type201.k m) (theta₂₁ m * theta₂₁ m) 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  refine MatEq.of_witness (W := !![8 * 2 ^ j, 1, 1; 1, 2 ^ j, 2 ^ j; 1, 2 ^ j, 2 ^ j])
    fun i l => ?_
  fin_cases i <;> fin_cases l <;>
    simp [show j + 2 - 1 = j + 1 from rfl, -mul_eq_zero, -mul_eq_mul_left_iff,
      -mul_eq_mul_right_iff] <;> ring1

theorem theta₁₁_theta₁₂_comm {m : ℕ} (hm : 2 ≤ m) :
    MatEq (Type201.k m) (theta₁₁ m * theta₁₂ m) (theta₁₂ m * theta₁₁ m) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  refine MatEq.of_witness (W := !![0, -4 * 2 ^ j, 4 * 2 ^ j; 0, -5 * 2 ^ j, 4 * 2 ^ j;
    0, -4 * 2 ^ j, 5 * 2 ^ j]) fun i l => ?_
  fin_cases i <;> fin_cases l <;>
    simp [show j + 2 - 1 = j + 1 from rfl, -mul_eq_zero, -mul_eq_mul_left_iff,
      -mul_eq_mul_right_iff] <;> ring1

theorem conjU_theta₁₁ {m : ℕ} (hm : 2 ≤ m) :
    MatEq (Type201.k m) (conjU (theta₁₁ m)) (theta₁₁ m) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  refine MatEq.of_witness (W := 0) fun i l => ?_
  fin_cases i <;> fin_cases l <;>
    simp [show j + 2 - 1 = j + 1 from rfl, -mul_eq_zero, -mul_eq_mul_left_iff,
      -mul_eq_mul_right_iff]

theorem conjU_theta₂₁ {m : ℕ} (hm : 2 ≤ m) :
    MatEq (Type201.k m) (conjU (theta₂₁ m)) (theta₂₁ m) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  refine MatEq.of_witness (W := 0) fun i l => ?_
  fin_cases i <;> fin_cases l <;>
    simp [show j + 2 - 1 = j + 1 from rfl, -mul_eq_zero, -mul_eq_mul_left_iff,
      -mul_eq_mul_right_iff]

theorem conjU_theta₁₂ {m : ℕ} (hm : 2 ≤ m) :
    MatEq (Type201.k m) (conjU (theta₁₂ m)) (theta₁₂ m * theta₁₁ m) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  refine MatEq.of_witness (W := !![-4 * 2 ^ j, -4 * 2 ^ j, -4 * 2 ^ j - 1;
    -4 * 2 ^ j - 1, -5 * 2 ^ j, -5 * 2 ^ j - 1; -4 * 2 ^ j, -4 * 2 ^ j, -4 * 2 ^ j - 1])
    fun i l => ?_
  fin_cases i <;> fin_cases l <;>
    simp [show j + 2 - 1 = j + 1 from rfl, -mul_eq_zero, -mul_eq_mul_left_iff,
      -mul_eq_mul_right_iff] <;> ring1

theorem conjU_theta₂₂ {m : ℕ} (hm : 2 ≤ m) :
    MatEq (Type201.k m) (conjU (theta₂₂ m)) (theta₂₂ m * theta₂₁ m * eMat m) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  refine MatEq.of_witness (W := !![-4 * 2 ^ j, -4 * 2 ^ j, -8 * 2 ^ j - 1;
    -1, -8 * (2 ^ j) ^ 2 - 2 ^ j, -8 * (2 ^ j) ^ 2 - 2 ^ j; -4 * 2 ^ j, 0, -4 * 2 ^ j - 1])
    fun i l => ?_
  fin_cases i <;> fin_cases l <;>
    simp [show j + 2 - 1 = j + 1 from rfl, -mul_eq_zero, -mul_eq_mul_left_iff,
      -mul_eq_mul_right_iff] <;> ring1

theorem uvM_matEq_type200 {m p : ℕ} (hp : p < m) :
    MatEq (Type200.k p) (Type201.uvM m) Type200.uvM := by
  obtain ⟨q, rfl⟩ : ∃ q, m = p + 1 + q := ⟨m - p - 1, by omega⟩
  refine MatEq.of_witness (W := !![0, 0, 0; 0, 0, 4 * 2 ^ p * (2 ^ q) ^ 2 + 3 * 2 ^ q;
    0, 2 ^ q, 0]) fun i l => ?_
  fin_cases i <;> fin_cases l <;>
    simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1

theorem tM_matEq_type200 {m p : ℕ} (hp : p < m) :
    MatEq (Type200.k p) (Type201.tM m) Type200.tM := by
  obtain ⟨q, rfl⟩ : ∃ q, m = p + 1 + q := ⟨m - p - 1, by omega⟩
  refine MatEq.of_witness (W := !![0, 0, -4 * 2 ^ q; 0, 2 ^ q, -2 ^ q; 0, 0, -2 ^ q])
    fun i l => ?_
  fin_cases i <;> fin_cases l <;>
    simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1

end

end Stroth34T201Ident

end CFSG.CGT.Stroth77
