module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1ClsUniLowBlock

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.UniLow

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KU7

variable {p f : ℕ} {K : Type} [Field K]

structure BlockOrder3 (h : UnitaryFieldData p f K) where
  B : Matrix (Fin 2) (Fin 2) K
  unitary : KU7.dagI h B * B = 1
  det_eq : B.det = 1
  cube : B ^ 3 = 1
  ns1 : ∀ c : K, B ≠ c • 1
  ns2 : ∀ c : K, B ^ 2 ≠ c • 1

theorem nonempty_blockOrder3 [Finite K] (h : UnitaryFieldData p f K) (h3 : (3 : K) ≠ 0) :
    Nonempty (BlockOrder3 h) := by
  obtain ⟨B, h1, h2, h3', h4, h5⟩ := exists_block h h3
  exact ⟨⟨B, h1, h2, h3', h4, h5⟩⟩

@[expose] def BlockOrder3.pw {h : UnitaryFieldData p f K} (β : BlockOrder3 h) (a : ZMod 3) :
    Matrix (Fin 2) (Fin 2) K :=
  β.B ^ a.val

theorem pow_eq_pow_mod_three (B : Matrix (Fin 2) (Fin 2) K) (hB3 : B ^ 3 = 1) (x : ℕ) :
    B ^ x = B ^ (x % 3) := by
  have hx := Nat.mod_add_div x 3
  calc B ^ x = B ^ (x % 3 + 3 * (x / 3)) := by rw [hx]
    _ = B ^ (x % 3) * (B ^ 3) ^ (x / 3) := by rw [pow_add, pow_mul]
    _ = B ^ (x % 3) := by rw [hB3, one_pow, mul_one]

theorem BlockOrder3.pw_add {h : UnitaryFieldData p f K} (β : BlockOrder3 h) (a b : ZMod 3) :
    β.pw (a + b) = β.pw a * β.pw b := by
  unfold BlockOrder3.pw
  rw [ZMod.val_add, ← pow_add, pow_eq_pow_mod_three β.B β.cube (a.val + b.val)]

theorem BlockOrder3.pw_zero {h : UnitaryFieldData p f K} (β : BlockOrder3 h) :
    β.pw 0 = 1 := by
  simp [BlockOrder3.pw]

theorem BlockOrder3.pw_det {h : UnitaryFieldData p f K} (β : BlockOrder3 h) (a : ZMod 3) :
    (β.pw a).det = 1 := by
  unfold BlockOrder3.pw
  rw [Matrix.det_pow, β.det_eq, one_pow]

theorem BlockOrder3.dagI_pow_mul_self {h : UnitaryFieldData p f K} (β : BlockOrder3 h) (n : ℕ) :
    KU7.dagI h (β.B ^ n) * β.B ^ n = 1 := by
  induction n with
  | zero => simp [KU7.dagI]
  | succ n ih =>
    rw [pow_succ', KU7.dagI_mul]
    calc KU7.dagI h (β.B ^ n) * KU7.dagI h β.B * (β.B * β.B ^ n)
        = KU7.dagI h (β.B ^ n) * (KU7.dagI h β.B * β.B) * β.B ^ n := by simp only [mul_assoc]
      _ = 1 := by rw [β.unitary, mul_one, ih]

theorem BlockOrder3.dagI_pw {h : UnitaryFieldData p f K} (β : BlockOrder3 h) (a : ZMod 3) :
    KU7.dagI h (β.pw a) * β.pw a = 1 :=
  β.dagI_pow_mul_self a.val

theorem BlockOrder3.pw_eq_smul_one {h : UnitaryFieldData p f K} (β : BlockOrder3 h) (a : ZMod 3)
    (c : K) (hc : β.pw a = c • 1) : a = 0 := by
  unfold BlockOrder3.pw at hc
  have hlt := ZMod.val_lt a
  rcases (show a.val = 0 ∨ a.val = 1 ∨ a.val = 2 by omega) with h0 | h1 | h2
  · exact (ZMod.val_eq_zero a).mp h0
  · rw [h1, pow_one] at hc
    exact absurd hc (β.ns1 c)
  · rw [h2] at hc
    exact absurd hc (β.ns2 c)

abbrev Tidx (r : ℕ) : Type := (Fin 2 × Fin 4) ⊕ Fin r

@[expose] def fullMat {h : UnitaryFieldData p f K} (β : BlockOrder3 h) (r : ℕ)
    (z : Fin 4 → ZMod 3) : Matrix (Tidx r) (Tidx r) K :=
  Matrix.fromBlocks (Matrix.blockDiagonal fun k => β.pw (z k)) 0 0 (1 : Matrix (Fin r) (Fin r) K)

theorem fullMat_mul {h : UnitaryFieldData p f K} (β : BlockOrder3 h) (r : ℕ)
    (z z' : Fin 4 → ZMod 3) : fullMat β r z * fullMat β r z' = fullMat β r (z + z') := by
  unfold fullMat
  rw [Matrix.fromBlocks_multiply, ← Matrix.blockDiagonal_mul]
  simp [BlockOrder3.pw_add]

theorem fullMat_zero {h : UnitaryFieldData p f K} (β : BlockOrder3 h) (r : ℕ) :
    fullMat β r 0 = 1 := by
  unfold fullMat
  simp only [Pi.zero_apply, BlockOrder3.pw_zero]
  rw [show (fun _ : Fin 4 => (1 : Matrix (Fin 2) (Fin 2) K)) = 1 from rfl, Matrix.blockDiagonal_one,
    Matrix.fromBlocks_one]

theorem fullMat_det {h : UnitaryFieldData p f K} (β : BlockOrder3 h) (r : ℕ) (z : Fin 4 → ZMod 3) :
    (fullMat β r z).det = 1 := by
  unfold fullMat
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_blockDiagonal, Matrix.det_one, mul_one]
  exact Finset.prod_eq_one fun k _ => β.pw_det (z k)

theorem fullMat_dagI {h : UnitaryFieldData p f K} (β : BlockOrder3 h) (r : ℕ)
    (z : Fin 4 → ZMod 3) : KU7.dagI h (fullMat β r z) * fullMat β r z = 1 := by
  have hpw : ∀ k, ((β.pw (z k)).map h.bar)ᵀ * β.pw (z k) = 1 := fun k => β.dagI_pw (z k)
  unfold KU7.dagI fullMat
  simp only [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, map_zero, map_one,
    Matrix.map_zero, Matrix.transpose_zero, Matrix.map_one, Matrix.transpose_one,
    Matrix.blockDiagonal_map, Matrix.blockDiagonal_transpose]
  rw [Matrix.fromBlocks_multiply, ← Matrix.blockDiagonal_mul]
  simp [hpw]
  rw [show (fun _ : Fin 4 => (1 : Matrix (Fin 2) (Fin 2) K)) = 1 from rfl, Matrix.blockDiagonal_one,
    Matrix.fromBlocks_one]

theorem fullMat_scalar {h : UnitaryFieldData p f K} (β : BlockOrder3 h) (r : ℕ)
    (z : Fin 4 → ZMod 3) (c : K) (hc : fullMat β r z = c • 1) : z = 0 := by
  funext k
  have hk : β.pw (z k) = c • 1 := by
    ext a b
    have := congrFun (congrFun hc (Sum.inl (a, k))) (Sum.inl (b, k))
    simpa [fullMat, Matrix.blockDiagonal_apply, Matrix.one_apply] using this
  exact β.pw_eq_smul_one (z k) c hk

@[expose] def eT (r : ℕ) : Fin (8 + r) ≃ Tidx r :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (finProdFinEquiv (m := 2) (n := 4)).symm (Equiv.refl _))

@[expose] def W {h : UnitaryFieldData p f K} (β : BlockOrder3 h) (r : ℕ) (z : Fin 4 → ZMod 3) :
    Matrix (Fin (8 + r)) (Fin (8 + r)) K :=
  (fullMat β r z).submatrix (eT r) (eT r)

theorem submatrix_mul_self_equiv {ι κ : Type} [Fintype ι] [Fintype κ] (M N : Matrix κ κ K)
    (e : ι ≃ κ) :
    (M.submatrix e e) * (N.submatrix e e) = (M * N).submatrix e e := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e (fun t => M (e i) t * N t (e j))

theorem W_mul {h : UnitaryFieldData p f K} (β : BlockOrder3 h) (r : ℕ) (z z' : Fin 4 → ZMod 3) :
    W β r z * W β r z' = W β r (z + z') := by
  unfold W
  rw [submatrix_mul_self_equiv, fullMat_mul]

theorem W_zero {h : UnitaryFieldData p f K} (β : BlockOrder3 h) (r : ℕ) :
    W β r 0 = 1 := by
  unfold W
  rw [fullMat_zero, Matrix.submatrix_one_equiv]

theorem W_det {h : UnitaryFieldData p f K} (β : BlockOrder3 h) (r : ℕ) (z : Fin 4 → ZMod 3) :
    (W β r z).det = 1 := by
  unfold W
  rw [Matrix.det_submatrix_equiv_self, fullMat_det]

theorem W_dagI {h : UnitaryFieldData p f K} (β : BlockOrder3 h) (r : ℕ) (z : Fin 4 → ZMod 3) :
    KU7.dagI h (W β r z) * W β r z = 1 := by
  unfold W
  rw [KU7.dagI_submatrix, submatrix_mul_self_equiv, fullMat_dagI, Matrix.submatrix_one_equiv]

theorem W_scalar {h : UnitaryFieldData p f K} (β : BlockOrder3 h) (r : ℕ) (z : Fin 4 → ZMod 3)
    (c : K) (hc : W β r z = c • 1) : z = 0 := by
  apply fullMat_scalar β r z c
  ext x y
  have := congrFun (congrFun hc ((eT r).symm x)) ((eT r).symm y)
  simpa [W, Matrix.one_apply] using this

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.UniLow

end
