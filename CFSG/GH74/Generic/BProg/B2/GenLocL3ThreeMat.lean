module

public import CFSG.GH74.Generic.BProg.B2.GenLocL3Pair
public import CFSG.GH74.Generic.BProg.B2.GenLocL3Seven

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.LocalAnalysis.ComponentInitial GenLocL3Pair
open scoped MatrixGroups


open CFSG CFSG.GH74 Subgroup CFSG.LocalAnalysis.ComponentInitial GenLocL3Pair
open scoped MatrixGroups

namespace GenLocL3Three

abbrev K3 : Type := ZMod 3

theorem card_K3 : Nat.card K3 = 3 := by simp

theorem sigma_eq_one (σ : K3 ≃+* K3) : σ = 1 :=
  GenLocL3Seven.eq_one_of_card_prime Nat.prime_three card_K3 σ

theorem scalars_eq_bot : LinearFlag.scalars 3 K3 = ⊥ := by
  ext A
  rw [LinearFlag.mem_scalars, Subgroup.mem_bot]
  constructor
  · rintro ⟨c, hc, hA⟩
    have key : ∀ c : K3ˣ, c ^ 3 = 1 → c = 1 := by decide
    have hc1 : c = 1 := key c hc
    subst hc1
    ext i j
    simp [hA, Matrix.one_apply]
  · rintro rfl
    exact ⟨1, one_pow _, by simp⟩

theorem proj_injective : Function.Injective (LinearFlag.proj 3 K3) := by
  intro g h hgh
  have := LinearFlag.proj_eq_proj_iff.1 hgh
  rw [scalars_eq_bot, Subgroup.mem_bot] at this
  exact inv_mul_eq_one.1 this

theorem conjAut_fixed_iff (A : GL (Fin 3) K3) (g : SL(3, K3)) :
    LinearFlag.conjAut 3 K3 A (LinearFlag.proj 3 K3 g) = LinearFlag.proj 3 K3 g ↔
      (A : Matrix (Fin 3) (Fin 3) K3) * (g : Matrix (Fin 3) (Fin 3) K3) =
        (g : Matrix (Fin 3) (Fin 3) K3) * A := by
  rw [LinearFlag.conjAut_proj]
  constructor
  · intro h
    have h' := proj_injective h
    have h2 := congrArg (fun x : SL(3, K3) => (x : Matrix (Fin 3) (Fin 3) K3)) h'
    simp only [LinearFlag.coe_slConjugation] at h2
    calc (A : Matrix (Fin 3) (Fin 3) K3) * g =
          (A * g * ((A⁻¹ : GL (Fin 3) K3) : Matrix (Fin 3) (Fin 3) K3)) * A := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
            Matrix.mul_one]
      _ = g * A := by rw [h2]
  · intro h
    congr 1
    apply Subtype.ext
    rw [LinearFlag.coe_slConjugation, h, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one]

theorem inv_transpose_mul_transpose (g : SL(3, K3)) :
    (((g⁻¹ : SL(3, K3)).transpose : SL(3, K3)) : Matrix (Fin 3) (Fin 3) K3) *
      (g : Matrix (Fin 3) (Fin 3) K3).transpose = 1 := by
  rw [Matrix.SpecialLinearGroup.coe_transpose, ← Matrix.transpose_mul,
    ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
    Matrix.transpose_one]

theorem transpose_mul_inv_transpose (g : SL(3, K3)) :
    (g : Matrix (Fin 3) (Fin 3) K3).transpose *
      (((g⁻¹ : SL(3, K3)).transpose : SL(3, K3)) : Matrix (Fin 3) (Fin 3) K3) = 1 := by
  rw [Matrix.SpecialLinearGroup.coe_transpose, ← Matrix.transpose_mul,
    ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
    Matrix.transpose_one]

theorem conjAut_dual_fixed_iff (A : GL (Fin 3) K3) (g : SL(3, K3)) :
    (LinearFlag.conjAut 3 K3 A * LinearFlag.dualAut 3 K3) (LinearFlag.proj 3 K3 g) =
      LinearFlag.proj 3 K3 g ↔
      (g : Matrix (Fin 3) (Fin 3) K3) * (A : Matrix (Fin 3) (Fin 3) K3) *
        (g : Matrix (Fin 3) (Fin 3) K3).transpose = A := by
  rw [MulAut.mul_apply, LinearFlag.dualAut_proj, LinearFlag.conjAut_proj]
  set H : Matrix (Fin 3) (Fin 3) K3 :=
    (((g⁻¹ : SL(3, K3)).transpose : SL(3, K3)) : Matrix (Fin 3) (Fin 3) K3) with hH
  have h1 : H * (g : Matrix (Fin 3) (Fin 3) K3).transpose = 1 := inv_transpose_mul_transpose g
  have h2 : (g : Matrix (Fin 3) (Fin 3) K3).transpose * H = 1 := transpose_mul_inv_transpose g
  constructor
  · intro h
    have h' := proj_injective h
    have h3 := congrArg (fun x : SL(3, K3) => (x : Matrix (Fin 3) (Fin 3) K3)) h'
    simp only [LinearFlag.coe_slConjugation] at h3
    have h4 : (A : Matrix (Fin 3) (Fin 3) K3) * H = (g : Matrix (Fin 3) (Fin 3) K3) * A := by
      calc (A : Matrix (Fin 3) (Fin 3) K3) * H
          = (A * H * ((A⁻¹ : GL (Fin 3) K3) : Matrix (Fin 3) (Fin 3) K3)) * A := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
              Matrix.mul_one]
        _ = g * A := by rw [hH, h3]
    calc (g : Matrix (Fin 3) (Fin 3) K3) * A * (g : Matrix (Fin 3) (Fin 3) K3).transpose
        = A * H * (g : Matrix (Fin 3) (Fin 3) K3).transpose := by rw [h4]
      _ = A := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  · intro h
    have h4 : (A : Matrix (Fin 3) (Fin 3) K3) * H = (g : Matrix (Fin 3) (Fin 3) K3) * A := by
      calc (A : Matrix (Fin 3) (Fin 3) K3) * H
          = ((g : Matrix (Fin 3) (Fin 3) K3) * A * (g : Matrix (Fin 3) (Fin 3) K3).transpose) * H := by
            rw [h]
        _ = g * A := by rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]
    congr 1
    apply Subtype.ext
    rw [LinearFlag.coe_slConjugation, ← hH, h4, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.mul_one]


@[expose] def tauU (k : Fin 3) : Fin 3 → K3ˣ := fun i => if i = k then -1 else 1

theorem tauU_val (k i : Fin 3) : ((tauU k i : K3ˣ) : K3) = if i = k then -1 else 1 := by
  unfold tauU
  split_ifs <;> simp

theorem comm_entry (u : Fin 3 → K3) (N : Matrix (Fin 3) (Fin 3) K3)
    (h : Matrix.diagonal u * N = N * Matrix.diagonal u) (i l : Fin 3) :
    (u i - u l) * N i l = 0 := by
  have := congrFun (congrFun h i) l
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal] at this
  linear_combination this

theorem zero_of_comm (k : Fin 3) (N : Matrix (Fin 3) (Fin 3) K3)
    (hc : Matrix.diagonal (fun i => ((tauU k i : K3ˣ) : K3)) * N =
      N * Matrix.diagonal (fun i => ((tauU k i : K3ˣ) : K3))) :
    ∀ i, i ≠ k → N i k = 0 ∧ N k i = 0 := by
  intro i hi
  have h1 := comm_entry _ N hc i k
  have h2 := comm_entry _ N hc k i
  simp only [tauU_val, hi, ↓reduceIte] at h1 h2
  have h2ne : ((1 : K3) - -1) ≠ 0 := by decide
  have h3ne : ((-1 : K3) - 1) ≠ 0 := by decide
  exact ⟨(mul_eq_zero.1 h1).resolve_left h2ne, (mul_eq_zero.1 h2).resolve_left h3ne⟩

theorem isDiag_of_comm2 {k m : Fin 3} (hkm : k ≠ m) (N : Matrix (Fin 3) (Fin 3) K3)
    (hk : Matrix.diagonal (fun i => ((tauU k i : K3ˣ) : K3)) * N =
      N * Matrix.diagonal (fun i => ((tauU k i : K3ˣ) : K3)))
    (hm : Matrix.diagonal (fun i => ((tauU m i : K3ˣ) : K3)) * N =
      N * Matrix.diagonal (fun i => ((tauU m i : K3ˣ) : K3))) : N.IsDiag := by
  have z1 := zero_of_comm k N hk
  have z2 := zero_of_comm m N hm
  intro i l hil
  have key : ∀ m m' i l : Fin 3, m ≠ m' → i ≠ l → (m = i ∨ m = l ∨ m' = i ∨ m' = l) := by decide
  rcases key k m i l hkm hil with h | h | h | h
  · subst h
    exact (z1 l hil.symm).2
  · subst h
    exact (z1 i hil).1
  · subst h
    exact (z2 l hil.symm).2
  · subst h
    exact (z2 i hil).1

theorem sq_eq_one_of_ne_zero : ∀ x : K3, x ≠ 0 → x ^ 2 = 1 := by decide

theorem diag_sq (N : Matrix (Fin 3) (Fin 3) K3) (hdiag : N.IsDiag) (hdet : N.det ≠ 0) : N ^ 2 = 1 := by
  have hND : N = Matrix.diagonal (Matrix.diag N) := hdiag.diagonal_diag.symm
  have hne : ∀ i, N i i ≠ 0 := by
    intro i
    rw [hND, Matrix.det_diagonal] at hdet
    exact (Finset.prod_ne_zero_iff.1 hdet) i (Finset.mem_univ i)
  rw [hND, Matrix.diagonal_pow]
  convert Matrix.diagonal_one (n := Fin 3) (α := K3) using 2
  ext i
  exact sq_eq_one_of_ne_zero _ (hne i)

@[expose] def blkE : Fin 3 → Matrix (Fin 2) (Fin 2) K3 → K3 → Matrix (Fin 3) (Fin 3) K3
  | 0, M, e => !![e, 0, 0; 0, M 0 0, M 0 1; 0, M 1 0, M 1 1]
  | 1, M, e => !![M 0 0, 0, M 0 1; 0, e, 0; M 1 0, 0, M 1 1]
  | 2, M, e => !![M 0 0, M 0 1, 0; M 1 0, M 1 1, 0; 0, 0, e]

theorem blkE_mul (m : Fin 3) (M M' : Matrix (Fin 2) (Fin 2) K3) (e e' : K3) :
    blkE m M e * blkE m M' e' = blkE m (M * M') (e * e') := by
  fin_cases m <;> (ext i j; fin_cases i <;> fin_cases j <;>
    simp [blkE, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three])

theorem blkE_one (m : Fin 3) : blkE m 1 1 = 1 := by
  fin_cases m <;> (ext i j; fin_cases i <;> fin_cases j <;> simp [blkE])

theorem blkE_pow (m : Fin 3) (M : Matrix (Fin 2) (Fin 2) K3) (e : K3) (n : ℕ) :
    (blkE m M e) ^ n = blkE m (M ^ n) (e ^ n) := by
  induction n with
  | zero => simp [blkE_one]
  | succ n ih => rw [pow_succ, ih, blkE_mul, pow_succ, pow_succ]

theorem o2_pow4 : ∀ a b c d p q : ZMod 3, p ≠ 0 → q ≠ 0 →
    a * p * a + b * q * b = p → a * p * c + b * q * d = 0 → c * p * c + d * q * d = q →
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) (ZMod 3)) ^ 4 = 1 := by decide

theorem esq4 (e p : K3) (hp : p ≠ 0) (h : e * p * e = p) : e ^ 4 = 1 := by
  have h3 : (e * e - 1) * p = 0 := by linear_combination h
  have h4 := (mul_eq_zero.1 h3).resolve_right hp
  have h5 : e * e = 1 := by linear_combination h4
  have : e ^ 4 = (e * e) ^ 2 := by ring
  rw [this, h5, one_pow]


theorem block_pow4 (m : Fin 3) (u' : Fin 3 → K3) (hu' : ∀ i, u' i ≠ 0) (N : Matrix (Fin 3) (Fin 3) K3)
    (hc : Matrix.diagonal (fun i => ((tauU m i : K3ˣ) : K3)) * N =
      N * Matrix.diagonal (fun i => ((tauU m i : K3ˣ) : K3)))
    (hd : N * Matrix.diagonal u' * N.transpose = Matrix.diagonal u') : N ^ 4 = 1 := by
  have hzero := zero_of_comm m N hc
  rcases (by decide : ∀ m : Fin 3, m = 0 ∨ m = 1 ∨ m = 2) m with rfl | rfl | rfl
  · obtain ⟨z01, z10⟩ := hzero 1 (by decide)
    obtain ⟨z02, z20⟩ := hzero 2 (by decide)
    have e00 := congrFun (congrFun hd 0) 0
    have e11 := congrFun (congrFun hd 1) 1
    have e12 := congrFun (congrFun hd 1) 2
    have e22 := congrFun (congrFun hd 2) 2
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_three, z01, z10, z02, z20] at e00 e11 e12 e22
    have hM := o2_pow4 (N 1 1) (N 1 2) (N 2 1) (N 2 2) (u' 1) (u' 2) (hu' 1) (hu' 2) e11 e12 e22
    have hN : N = blkE 0 !![N 1 1, N 1 2; N 2 1, N 2 2] (N 0 0) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [blkE, z01, z10, z02, z20]
    rw [hN, blkE_pow, hM, esq4 _ _ (hu' 0) e00, blkE_one]
  · obtain ⟨z01, z10⟩ := hzero 0 (by decide)
    obtain ⟨z21, z12⟩ := hzero 2 (by decide)
    have e00 := congrFun (congrFun hd 0) 0
    have e11 := congrFun (congrFun hd 1) 1
    have e02 := congrFun (congrFun hd 0) 2
    have e22 := congrFun (congrFun hd 2) 2
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_three, z01, z10, z21, z12] at e00 e11 e02 e22
    have hM := o2_pow4 (N 0 0) (N 0 2) (N 2 0) (N 2 2) (u' 0) (u' 2) (hu' 0) (hu' 2) e00 e02 e22
    have hN : N = blkE 1 !![N 0 0, N 0 2; N 2 0, N 2 2] (N 1 1) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [blkE, z01, z10, z21, z12]
    rw [hN, blkE_pow, hM, esq4 _ _ (hu' 1) e11, blkE_one]
  · obtain ⟨z02, z20⟩ := hzero 0 (by decide)
    obtain ⟨z12, z21⟩ := hzero 1 (by decide)
    have e00 := congrFun (congrFun hd 0) 0
    have e01 := congrFun (congrFun hd 0) 1
    have e11 := congrFun (congrFun hd 1) 1
    have e22 := congrFun (congrFun hd 2) 2
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_three, z02, z20, z12, z21] at e00 e01 e11 e22
    have hM := o2_pow4 (N 0 0) (N 0 1) (N 1 0) (N 1 1) (u' 0) (u' 1) (hu' 0) (hu' 1) e00 e01 e11
    have hN : N = blkE 2 !![N 0 0, N 0 1; N 1 0, N 1 1] (N 2 2) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [blkE, z02, z20, z12, z21]
    rw [hN, blkE_pow, hM, esq4 _ _ (hu' 2) e22, blkE_one]

theorem pow_of_matrix {n : ℕ} {g : SL(3, K3)} (h : (g : Matrix (Fin 3) (Fin 3) K3) ^ n = 1) :
    LinearFlag.proj 3 K3 g ^ n = 1 := by
  rw [← map_pow]
  have : (g ^ n : SL(3, K3)) = 1 := Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_pow, h]; rfl)
  rw [this, map_one]

end GenLocL3Three
end CFSG.GH74.Generic.BProg.B2
