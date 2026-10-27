module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviSUThree

public section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.CentralizerMatrix

open Matrix CFSG.AGLEmbedding
open scoped Kronecker

variable {K : Type} [Field K] {ζ : K}

theorem eq_scalar_of_commute_heis (hζ : IsPrimitiveRoot ζ 3) {M : Matrix (Fin 3) (Fin 3) K}
    (hX : M * heisXMat ζ = heisXMat ζ * M) (hY : M * heisYMat = heisYMat * M) :
    M = Matrix.scalar (Fin 3) (M 0 0) := by
  have h3 := hζ.pow_eq_one
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by norm_num)
  have hζ2 : ζ ^ 2 ≠ 1 := fun h => by
    have := (hζ.pow_eq_one_iff_dvd 2).1 h
    omega
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have hζ3 : ζ ^ 2 ≠ ζ := fun h => hζ1 (mul_left_cancel₀ hζ0 (by rw [← sq, h, mul_one]))
  have e : ∀ i j, (M * heisXMat ζ) i j = (heisXMat ζ * M) i j := fun i j =>
    congrFun (congrFun hX i) j
  have f : ∀ i j, (M * (heisYMat : Matrix (Fin 3) (Fin 3) K)) i j =
      ((heisYMat : Matrix (Fin 3) (Fin 3) K) * M) i j := fun i j =>
    congrFun (congrFun hY i) j
  simp [heisXMat, heisYMat, Matrix.mul_apply, Fin.sum_univ_three] at e f
  have h01 := e 0 1
  have h02 := e 0 2
  have h10 := e 1 0
  have h12 := e 1 2
  have h20 := e 2 0
  have h21 := e 2 1
  have g00 := f 1 0
  have g11 := f 2 1
  simp at h01 h02 h10 h12 h20 h21 g00 g11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply] <;> grind

theorem mul_heisXMat_apply (B : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    (B * heisXMat ζ) i j = B i j * ![1, ζ, ζ ^ 2] j := by
  fin_cases j <;> simp [heisXMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem heisXMat_mul_apply (B : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    (heisXMat ζ * B) i j = ![1, ζ, ζ ^ 2] i * B i j := by
  fin_cases i <;> simp [heisXMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct]

theorem mul_heisYMat_apply (B : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    (B * (heisYMat : Matrix (Fin 3) (Fin 3) K)) i j = B i (j + 1) := by
  fin_cases j <;> simp [heisYMat, Matrix.mul_apply, Fin.sum_univ_three] <;> rfl

theorem heisYMat_mul_apply (B : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    ((heisYMat : Matrix (Fin 3) (Fin 3) K) * B) i j = B (i + 2) j := by
  fin_cases i <;> simp [heisYMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct] <;>
    rfl

theorem heisXMat_eq_diagonal : heisXMat ζ = Matrix.diagonal ![1, ζ, ζ ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heisXMat]

theorem heisYMat_pow_apply (b : ℕ) (i j : Fin 3) :
    ((heisYMat : Matrix (Fin 3) (Fin 3) K) ^ b) i j =
      if (i : ℕ) = ((j : ℕ) + b) % 3 then 1 else 0 := by
  induction b generalizing j with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    congr 1
    apply propext
    rw [add_zero, Nat.mod_eq_of_lt j.2]
    exact Fin.val_inj.symm
  | succ b ih =>
    rw [pow_succ, mul_heisYMat_apply, ih]
    congr 1
    apply propext
    rw [Fin.val_add]
    have := j.2
    constructor <;> intro h <;> omega

theorem heis_pow_mul_apply (a b : ℕ) (i j : Fin 3) :
    (heisXMat ζ ^ a * (heisYMat : Matrix (Fin 3) (Fin 3) K) ^ b) i j =
      ![1, ζ, ζ ^ 2] i ^ a * if (i : ℕ) = ((j : ℕ) + b) % 3 then 1 else 0 := by
  rw [heisXMat_eq_diagonal, Matrix.diagonal_pow, Matrix.diagonal_mul, heisYMat_pow_apply]
  rfl

theorem eq_smul_heis_of_twisted (hζ : IsPrimitiveRoot ζ 3) {B : Matrix (Fin 3) (Fin 3) K}
    {μ ν : K} (hμ : μ ^ 3 = 1) (hν : ν ^ 3 = 1)
    (hX : B * heisXMat ζ = μ • (heisXMat ζ * B))
    (hY : B * heisYMat = ν • ((heisYMat : Matrix (Fin 3) (Fin 3) K) * B)) :
    ∃ (a b : ℕ) (r : K), B = r • (heisXMat ζ ^ a * (heisYMat : Matrix (Fin 3) (Fin 3) K) ^ b) := by
  have h3 := hζ.pow_eq_one
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by norm_num)
  have hζ2 : ζ ^ 2 ≠ 1 := fun h => by
    have := (hζ.pow_eq_one_iff_dvd 2).1 h
    omega
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have hζ3 : ζ ^ 2 ≠ ζ := fun h => hζ1 (mul_left_cancel₀ hζ0 (by rw [← sq, h, mul_one]))
  have h4 : ζ ^ 4 = ζ := by rw [pow_succ, h3, one_mul]
  have e : ∀ i j, B i j * ![1, ζ, ζ ^ 2] j = μ * (![1, ζ, ζ ^ 2] i * B i j) := fun i j => by
    have := congrFun (congrFun hX i) j
    rwa [Matrix.smul_apply, mul_heisXMat_apply, heisXMat_mul_apply, smul_eq_mul] at this
  have f : ∀ i j, B i (j + 1) = ν * B (i + 2) j := fun i j => by
    have := congrFun (congrFun hY i) j
    rwa [Matrix.smul_apply, mul_heisYMat_apply, heisYMat_mul_apply, smul_eq_mul] at this
  obtain ⟨k, hk, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
  obtain ⟨l, hl, rfl⟩ := hζ.eq_pow_of_pow_eq_one hν
  have e00 : B 0 0 * 1 = ζ ^ k * (1 * B 0 0) := e 0 0
  have e01 : B 0 1 * ζ = ζ ^ k * (1 * B 0 1) := e 0 1
  have e02 : B 0 2 * ζ ^ 2 = ζ ^ k * (1 * B 0 2) := e 0 2
  have e10 : B 1 0 * 1 = ζ ^ k * (ζ * B 1 0) := e 1 0
  have e11 : B 1 1 * ζ = ζ ^ k * (ζ * B 1 1) := e 1 1
  have e12 : B 1 2 * ζ ^ 2 = ζ ^ k * (ζ * B 1 2) := e 1 2
  have e20 : B 2 0 * 1 = ζ ^ k * (ζ ^ 2 * B 2 0) := e 2 0
  have e21 : B 2 1 * ζ = ζ ^ k * (ζ ^ 2 * B 2 1) := e 2 1
  have e22 : B 2 2 * ζ ^ 2 = ζ ^ k * (ζ ^ 2 * B 2 2) := e 2 2
  have f00 : B 0 1 = ζ ^ l * B 2 0 := f 0 0
  have f01 : B 0 2 = ζ ^ l * B 2 1 := f 0 1
  have f02 : B 0 0 = ζ ^ l * B 2 2 := f 0 2
  have f10 : B 1 1 = ζ ^ l * B 0 0 := f 1 0
  have f11 : B 1 2 = ζ ^ l * B 0 1 := f 1 1
  have f12 : B 1 0 = ζ ^ l * B 0 2 := f 1 2
  have f20 : B 2 1 = ζ ^ l * B 1 0 := f 2 0
  have f21 : B 2 2 = ζ ^ l * B 1 1 := f 2 1
  have f22 : B 2 0 = ζ ^ l * B 1 2 := f 2 2
  clear e f hX hY
  interval_cases k <;> interval_cases l
  · refine ⟨0, 0, B 0 0, ?_⟩
    ext i j
    rw [Matrix.smul_apply, heis_pow_mul_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> simp <;> grind
  · refine ⟨1, 0, B 0 0, ?_⟩
    ext i j
    rw [Matrix.smul_apply, heis_pow_mul_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> simp <;> grind
  · refine ⟨2, 0, B 0 0, ?_⟩
    ext i j
    rw [Matrix.smul_apply, heis_pow_mul_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> simp <;> grind
  · refine ⟨0, 2, B 0 1, ?_⟩
    ext i j
    rw [Matrix.smul_apply, heis_pow_mul_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> simp <;> grind
  · refine ⟨1, 2, B 0 1, ?_⟩
    ext i j
    rw [Matrix.smul_apply, heis_pow_mul_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> simp <;> grind
  · refine ⟨2, 2, B 0 1, ?_⟩
    ext i j
    rw [Matrix.smul_apply, heis_pow_mul_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> simp <;> grind
  · refine ⟨0, 1, B 0 2, ?_⟩
    ext i j
    rw [Matrix.smul_apply, heis_pow_mul_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> simp <;> grind
  · refine ⟨1, 1, B 0 2, ?_⟩
    ext i j
    rw [Matrix.smul_apply, heis_pow_mul_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> simp <;> grind
  · refine ⟨2, 1, B 0 2, ?_⟩
    ext i j
    rw [Matrix.smul_apply, heis_pow_mul_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> simp <;> grind

theorem one_kronecker_mul_apply (A : Matrix (Fin 3) (Fin 3) K)
    (N : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) K) (i i' : Fin 2) (j j' : Fin 3) :
    (((1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ A) * N) (i, j) (i', j') =
      (A * Matrix.of fun l l' => N (i, l) (i', l')) j j' := by
  fin_cases i <;> fin_cases i' <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Fin.sum_univ_two]

theorem mul_one_kronecker_apply (A : Matrix (Fin 3) (Fin 3) K)
    (N : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) K) (i i' : Fin 2) (j j' : Fin 3) :
    (N * ((1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ A)) (i, j) (i', j') =
      ((Matrix.of fun l l' => N (i, l) (i', l')) * A) j j' := by
  fin_cases i <;> fin_cases i' <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Fin.sum_univ_two]

theorem eq_kronecker_one_of_commute (hζ : IsPrimitiveRoot ζ 3)
    {N : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) K}
    (hX : N * ((1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ heisXMat ζ) =
      ((1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ heisXMat ζ) * N)
    (hY : N * ((1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ heisYMat) =
      ((1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ heisYMat) * N) :
    N = (Matrix.of fun i i' => N (i, 0) (i', 0)) ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  set Q : Matrix (Fin 3) (Fin 3) K := Matrix.of fun l l' => N (i, l) (i', l') with hQ
  have hQX : Q * heisXMat ζ = heisXMat ζ * Q := by
    ext l l'
    rw [← mul_one_kronecker_apply, ← one_kronecker_mul_apply, hX]
  have hQY : Q * heisYMat = heisYMat * Q := by
    ext l l'
    rw [← mul_one_kronecker_apply, ← one_kronecker_mul_apply, hY]
  have hs := eq_scalar_of_commute_heis hζ hQX hQY
  have := congrFun (congrFun hs j) j'
  rw [Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.of_apply]
  change Q j j' = Q 0 0 * if j = j' then 1 else 0
  rw [this, Matrix.scalar_apply, Matrix.diagonal_apply, mul_ite, mul_one, mul_zero]

end CFSG.LieType.Chevalley.E7Three.CentralizerMatrix
