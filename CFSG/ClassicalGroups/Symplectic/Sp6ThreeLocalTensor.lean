module

public import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalDefs

public section

namespace CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal

open Matrix CFSG.Open CFSG.Open.StatedAPI CFSG.LinearAlgebra
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def tensorMatrix (A : Matrix (Fin 2) (Fin 2) K) (B : Matrix (Fin 3) (Fin 3) K) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  fromBlocks (A 0 0 • B) (A 0 1 • B) (A 1 0 • B) (A 1 1 • B)

theorem tensorMatrix_mul (A A' : Matrix (Fin 2) (Fin 2) K) (B B' : Matrix (Fin 3) (Fin 3) K) :
    tensorMatrix A B * tensorMatrix A' B' = tensorMatrix (A * A') (B * B') := by
  unfold tensorMatrix
  rw [fromBlocks_multiply]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1 <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_smul, mul_comm]

theorem tensorMatrix_one : tensorMatrix (1 : Matrix (Fin 2) (Fin 2) K) 1 = 1 := by
  unfold tensorMatrix
  simp [fromBlocks_one]

theorem tensorMatrix_transpose (A : Matrix (Fin 2) (Fin 2) K) (B : Matrix (Fin 3) (Fin 3) K) :
    (tensorMatrix A B)ᵀ = tensorMatrix Aᵀ Bᵀ := by
  unfold tensorMatrix
  rw [fromBlocks_transpose]
  simp [Matrix.transpose_smul]

theorem tensorMatrix_add_left (A A' : Matrix (Fin 2) (Fin 2) K) (B : Matrix (Fin 3) (Fin 3) K) :
    tensorMatrix (A + A') B = tensorMatrix A B + tensorMatrix A' B := by
  unfold tensorMatrix
  rw [fromBlocks_add]
  simp [add_smul]

theorem tensorMatrix_add_right (A : Matrix (Fin 2) (Fin 2) K) (B B' : Matrix (Fin 3) (Fin 3) K) :
    tensorMatrix A (B + B') = tensorMatrix A B + tensorMatrix A B' := by
  unfold tensorMatrix
  rw [fromBlocks_add]
  simp [smul_add]

theorem tensorMatrix_smul_left (c : K) (A : Matrix (Fin 2) (Fin 2) K)
    (B : Matrix (Fin 3) (Fin 3) K) : tensorMatrix (c • A) B = c • tensorMatrix A B := by
  unfold tensorMatrix
  rw [fromBlocks_smul]
  simp [smul_smul]

theorem tensorMatrix_smul_right (c : K) (A : Matrix (Fin 2) (Fin 2) K)
    (B : Matrix (Fin 3) (Fin 3) K) : tensorMatrix A (c • B) = c • tensorMatrix A B := by
  unfold tensorMatrix
  rw [fromBlocks_smul]
  simp [smul_smul, mul_comm]

theorem tensorMatrix_zero_left (B : Matrix (Fin 3) (Fin 3) K) : tensorMatrix 0 B = 0 := by
  unfold tensorMatrix
  simp

theorem tensorMatrix_zero_right (A : Matrix (Fin 2) (Fin 2) K) : tensorMatrix A 0 = 0 := by
  unfold tensorMatrix
  simp

theorem exists_sq_add_sq_eq_neg_three {r : ℕ} (hr : r.Prime) [CharP K r] [Finite K] :
    ∃ p q : K, p ^ 2 + q ^ 2 = -3 := by
  haveI : NeZero r := ⟨hr.ne_zero⟩
  obtain ⟨a, b, h⟩ := CharP.sq_add_sq K r (-3)
  exact ⟨a, b, by simpa using h⟩

theorem exists_sq_add_sq_eq_neg_one {r : ℕ} (hr : r.Prime) [CharP K r] [Finite K] :
    ∃ a b : K, a ^ 2 + b ^ 2 + 1 = 0 := by
  haveI : NeZero r := ⟨hr.ne_zero⟩
  obtain ⟨a, b, h⟩ := CharP.sq_add_sq K r (-1)
  exact ⟨a, b, by linear_combination (by simpa using h : (a : K) ^ 2 + (b : K) ^ 2 = -1)⟩

theorem exists_isotropic [Finite K] : ∃ a b : K, a ^ 2 + b ^ 2 + 1 = 0 :=
  exists_sq_add_sq_eq_neg_one (CharP.prime_ringChar K)

theorem blockMatrix_const (A : Matrix (Fin 2) (Fin 2) K) :
    blockMatrix (fun _ => A) = tensorMatrix A 1 := by
  unfold blockMatrix tensorMatrix
  simp [Matrix.smul_one_eq_diagonal]

theorem blockMatrix_vec_const (A : Matrix (Fin 2) (Fin 2) K) :
    blockMatrix ![A, A, A] = tensorMatrix A 1 := by
  rw [← blockMatrix_const]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem blockMatrix_pair (A A' : Matrix (Fin 2) (Fin 2) K) :
    blockMatrix ![A, A, A'] = tensorMatrix A (diagonal ![1, 1, 0]) +
      tensorMatrix A' (diagonal ![0, 0, 1]) := by
  unfold blockMatrix tensorMatrix
  rw [fromBlocks_add]
  congr 1 <;> (ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply])

theorem fromBlocks_form_eq_tensorMatrix :
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) =
      tensorMatrix !![0, 1; -1, 0] 1 := by
  unfold tensorMatrix
  simp

theorem transpose_mul_J₂_mul (A : Matrix (Fin 2) (Fin 2) K) :
    Aᵀ * !![0, 1; -1, 0] * A = A.det • !![0, 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

theorem skewPart_adjoint {s : SL(2, K)} (hs : IsCubeRootBlock s) :
    ((2 : K) • (s : Matrix (Fin 2) (Fin 2) K) + 1)ᵀ * !![0, 1; -1, 0] +
      !![0, 1; -1, 0] * ((2 : K) • (s : Matrix (Fin 2) (Fin 2) K) + 1) = 0 := by
  have hdet : (s : Matrix (Fin 2) (Fin 2) K).det = 1 := s.2
  have h1 : (s : Matrix (Fin 2) (Fin 2) K)ᵀ * !![0, 1; -1, 0] * (s : Matrix (Fin 2) (Fin 2) K) =
      !![0, 1; -1, 0] := by
    rw [transpose_mul_J₂_mul, hdet, one_smul]
  have h3 : (s : Matrix (Fin 2) (Fin 2) K) ^ 3 = 1 := by
    have := hs.pow_three
    simpa using congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K)) this
  have h2 : (s : Matrix (Fin 2) (Fin 2) K)ᵀ * !![0, 1; -1, 0] =
      !![0, 1; -1, 0] * (s : Matrix (Fin 2) (Fin 2) K) ^ 2 := by
    calc (s : Matrix (Fin 2) (Fin 2) K)ᵀ * !![0, 1; -1, 0]
        = (s : Matrix (Fin 2) (Fin 2) K)ᵀ * !![0, 1; -1, 0] *
            (s : Matrix (Fin 2) (Fin 2) K) ^ 3 := by rw [h3, Matrix.mul_one]
      _ = (s : Matrix (Fin 2) (Fin 2) K)ᵀ * !![0, 1; -1, 0] * (s : Matrix (Fin 2) (Fin 2) K) *
            (s : Matrix (Fin 2) (Fin 2) K) ^ 2 := by noncomm_ring
      _ = _ := by rw [h1]
  have h4 := hs.sq_add_self_add_one
  calc ((2 : K) • (s : Matrix (Fin 2) (Fin 2) K) + 1)ᵀ * !![0, 1; -1, 0] +
      !![0, 1; -1, 0] * ((2 : K) • (s : Matrix (Fin 2) (Fin 2) K) + 1)
      = (2 : K) • ((s : Matrix (Fin 2) (Fin 2) K)ᵀ * !![0, 1; -1, 0]) + !![0, 1; -1, 0] +
        ((2 : K) • (!![0, 1; -1, 0] * (s : Matrix (Fin 2) (Fin 2) K)) + !![0, 1; -1, 0]) := by
        simp [Matrix.transpose_add, Matrix.transpose_smul, Matrix.add_mul, Matrix.mul_add,
          Matrix.smul_mul, Matrix.mul_smul]
    _ = (2 : K) • (!![0, 1; -1, 0] * ((s : Matrix (Fin 2) (Fin 2) K) ^ 2 +
          (s : Matrix (Fin 2) (Fin 2) K) + 1)) := by
        rw [h2]
        simp only [Matrix.mul_add, Matrix.mul_one, smul_add, two_smul]
        abel
    _ = 0 := by rw [h4, Matrix.mul_zero, smul_zero]

theorem coe_block_vec (a b c : SL(2, K)) :
    (((block ![a, b, c] : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) =
      blockMatrix ![(a : Matrix (Fin 2) (Fin 2) K), (b : Matrix (Fin 2) (Fin 2) K),
        (c : Matrix (Fin 2) (Fin 2) K)] := by
  rw [coe_block]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem symplectic_one_add {X : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K}
    (hX : Xᵀ * fromBlocks 0 1 (-1) 0 + fromBlocks 0 1 (-1) 0 * X = 0) (hX2 : X * X = 0) :
    (1 + X)ᵀ * fromBlocks 0 1 (-1) 0 * (1 + X) = fromBlocks 0 1 (-1) 0 := by
  have h1 : Xᵀ * fromBlocks 0 1 (-1) 0 = -(fromBlocks 0 1 (-1) 0 * X) :=
    eq_neg_of_add_eq_zero_left hX
  have h2 : Xᵀ * fromBlocks 0 1 (-1) 0 * X = 0 := by
    rw [h1, neg_mul, Matrix.mul_assoc, hX2, Matrix.mul_zero, neg_zero]
  calc (1 + X)ᵀ * fromBlocks 0 1 (-1) 0 * (1 + X)
      = fromBlocks 0 1 (-1) 0 + (Xᵀ * fromBlocks 0 1 (-1) 0 + fromBlocks 0 1 (-1) 0 * X)
          + Xᵀ * fromBlocks 0 1 (-1) 0 * X := by
        rw [Matrix.transpose_add, Matrix.transpose_one]
        noncomm_ring
    _ = fromBlocks 0 1 (-1) 0 := by rw [hX, h2]; simp

@[expose] noncomputable def mkSp (g g' : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)
    (h₁ : g * g' = 1) (h₂ : g' * g = 1)
    (hJ : gᵀ * fromBlocks 0 1 (-1) 0 * g = fromBlocks 0 1 (-1) 0) : StatedSp 3 K :=
  ⟨⟨g, g', h₁, h₂⟩, by
    rw [mem_statedSp_iff]
    exact hJ⟩

@[simp] theorem coe_mkSp (g g' : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)
    (h₁ : g * g' = 1) (h₂ : g' * g = 1)
    (hJ : gᵀ * fromBlocks 0 1 (-1) 0 * g = fromBlocks 0 1 (-1) 0) :
    (((mkSp g g' h₁ h₂ hJ : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) = g :=
  rfl

@[expose] noncomputable def unipotentSp (X : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)
    (hX : Xᵀ * fromBlocks 0 1 (-1) 0 + fromBlocks 0 1 (-1) 0 * X = 0) (hX2 : X * X = 0) :
    StatedSp 3 K :=
  mkSp (1 + X) (1 - X)
    (by
      calc (1 + X) * (1 - X) = 1 - X * X := by noncomm_ring
        _ = 1 := by rw [hX2, sub_zero])
    (by
      calc (1 - X) * (1 + X) = 1 - X * X := by noncomm_ring
        _ = 1 := by rw [hX2, sub_zero])
    (symplectic_one_add hX hX2)

theorem coe_unipotentSp (X : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)
    (hX : Xᵀ * fromBlocks 0 1 (-1) 0 + fromBlocks 0 1 (-1) 0 * X = 0) (hX2 : X * X = 0) :
    (((unipotentSp X hX hX2 : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) = 1 + X :=
  rfl

theorem coe_unipotentSp_pow (X : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)
    (hX : Xᵀ * fromBlocks 0 1 (-1) 0 + fromBlocks 0 1 (-1) 0 * X = 0) (hX2 : X * X = 0)
    (n : ℕ) :
    ((((unipotentSp X hX hX2) ^ n : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) = 1 + (n : K) • X := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Subgroup.coe_mul, Units.val_mul, ih, coe_unipotentSp]
    calc (1 + (n : K) • X) * (1 + X) = 1 + ((n : K) + 1) • X + (n : K) • (X * X) := by
          simp only [add_smul, smul_add, one_smul, Matrix.add_mul, Matrix.mul_add,
            Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul]
          abel
      _ = 1 + ((n + 1 : ℕ) : K) • X := by rw [hX2, smul_zero, add_zero, Nat.cast_succ]

theorem one_add_smul_mul_one_add {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n K} (hX2 : X * X = 0) (c d : K) :
    (1 + c • X) * (1 + d • X) = 1 + (c + d) • X := by
  simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    hX2, smul_zero, add_zero, add_smul]
  abel

theorem coe_unipotentSp_inv (X : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)
    (hX : Xᵀ * fromBlocks 0 1 (-1) 0 + fromBlocks 0 1 (-1) 0 * X = 0) (hX2 : X * X = 0) :
    ((((unipotentSp X hX hX2)⁻¹ : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) = 1 - X :=
  rfl

theorem coe_unipotentSp_zpow (X : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)
    (hX : Xᵀ * fromBlocks 0 1 (-1) 0 + fromBlocks 0 1 (-1) 0 * X = 0) (hX2 : X * X = 0)
    (k : ℤ) :
    ((((unipotentSp X hX hX2) ^ k : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) = 1 + (k : K) • X := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [_root_.zpow_add_one, Subgroup.coe_mul, Units.val_mul, ih, coe_unipotentSp]
    have h1 : (1 + X : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) = 1 + (1 : K) • X := by
      rw [one_smul]
    rw [h1, one_add_smul_mul_one_add hX2]
    push_cast
    rfl
  | pred n ih =>
    rw [_root_.zpow_sub_one, Subgroup.coe_mul, Units.val_mul, ih, coe_unipotentSp_inv]
    have h1 : (1 - X : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) = 1 + (-1 : K) • X := by
      rw [neg_smul, one_smul, sub_eq_add_neg]
    rw [h1, one_add_smul_mul_one_add hX2]
    congr 2
    push_cast
    ring

theorem orderOf_unipotentSp {r : ℕ} (hr : r.Prime) [CharP K r]
    (X : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)
    (hX : Xᵀ * fromBlocks 0 1 (-1) 0 + fromBlocks 0 1 (-1) 0 * X = 0) (hX2 : X * X = 0)
    (hX0 : X ≠ 0) : orderOf (unipotentSp X hX hX2) = r := by
  haveI := Fact.mk hr
  refine orderOf_eq_prime ?_ ?_
  · apply Subtype.ext
    apply Units.ext
    rw [coe_unipotentSp_pow, CharP.cast_eq_zero, zero_smul, add_zero]
    rfl
  · intro h
    have h' := congrArg (fun g : StatedSp 3 K => (((g : GL (Fin 3 ⊕ Fin 3) K) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K))) h
    simp only [coe_unipotentSp] at h'
    exact hX0 (by simpa using h')

@[expose] noncomputable def orthBlock (M : Matrix (Fin 3) (Fin 3) K) (hM : Mᵀ * M = 1) :
    StatedSp 3 K :=
  mkSp (tensorMatrix 1 M) (tensorMatrix 1 Mᵀ)
    (by rw [tensorMatrix_mul, Matrix.one_mul, mul_eq_one_comm.mp hM, tensorMatrix_one])
    (by rw [tensorMatrix_mul, Matrix.one_mul, hM, tensorMatrix_one])
    (by
      rw [tensorMatrix_transpose, fromBlocks_form_eq_tensorMatrix, tensorMatrix_mul,
        tensorMatrix_mul]
      simp [hM])

theorem coe_orthBlock (M : Matrix (Fin 3) (Fin 3) K) (hM : Mᵀ * M = 1) :
    (((orthBlock M hM : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) = tensorMatrix 1 M :=
  rfl

theorem coe_orthBlock_pow (M : Matrix (Fin 3) (Fin 3) K) (hM : Mᵀ * M = 1) (n : ℕ) :
    ((((orthBlock M hM) ^ n : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) = tensorMatrix 1 (M ^ n) := by
  induction n with
  | zero => simpa using tensorMatrix_one.symm
  | succ n ih =>
    rw [pow_succ, Subgroup.coe_mul, Units.val_mul, ih, coe_orthBlock, tensorMatrix_mul,
      Matrix.one_mul, pow_succ]

theorem orderOf_orthBlock {r : ℕ} (hr : r.Prime) (M : Matrix (Fin 3) (Fin 3) K)
    (hM : Mᵀ * M = 1) (hMr : M ^ r = 1) (hM1 : M ≠ 1) : orderOf (orthBlock M hM) = r := by
  haveI := Fact.mk hr
  refine orderOf_eq_prime ?_ ?_
  · apply Subtype.ext
    apply Units.ext
    rw [coe_orthBlock_pow, hMr, tensorMatrix_one]
    rfl
  · intro h
    have h' := congrArg (fun g : StatedSp 3 K => (((g : GL (Fin 3 ⊕ Fin 3) K) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K))) h
    simp only [coe_orthBlock] at h'
    apply hM1
    ext i j
    have := congrFun (congrFun h' (Sum.inl i)) (Sum.inl j)
    simpa [tensorMatrix, Matrix.one_apply] using this

theorem commute_c₀_point_111_orthBlock {s : SL(2, K)} (hs : IsCubeRootBlock s)
    (M : Matrix (Fin 3) (Fin 3) K) (hM : Mᵀ * M = 1) :
    Commute (c₀ hs (Multiplicative.ofAdd ![1, 1, 1])) (orthBlock M hM) := by
  rw [commute_iff_coe_commute, c₀_point_111, coe_block_vec, blockMatrix_vec_const, coe_orthBlock]
  unfold Commute SemiconjBy
  rw [tensorMatrix_mul, tensorMatrix_mul, Matrix.mul_one, Matrix.one_mul, Matrix.one_mul,
    Matrix.mul_one]

end CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal

