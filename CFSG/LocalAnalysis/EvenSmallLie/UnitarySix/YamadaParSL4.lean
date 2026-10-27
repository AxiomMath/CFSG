module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParSUF4
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParLiftSL
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParModel
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParSurvData

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

open Matrix CFSG.Fischer

abbrev SL4 : Type := Matrix.SpecialLinearGroup (Fin 4) F4

theorem f4_ext {x y : F4} (h : x.code = y.code) : x = y := by
  cases x; cases y; cases h; rfl

theorem f4mat_ext {A B : Matrix (Fin 4) (Fin 4) F4} (h : ∀ i j, (A i j).code = (B i j).code) :
    A = B :=
  Matrix.ext fun i j => f4_ext (h i j)

@[expose] def frobF4 : F4 →+* F4 where
  toFun x := x * x
  map_one' := f4_ext (by decide)
  map_mul' x y := f4_ext (by revert x y; decide)
  map_zero' := f4_ext (by decide)
  map_add' x y := f4_ext (by revert x y; decide)

theorem frobF4_apply (x : F4) : frobF4 x = x * x := rfl

theorem frobF4_frobF4 (x : F4) : frobF4 (frobF4 x) = x := f4_ext (by revert x; decide)

theorem piJ_piJ (i : Fin 4) : piJ (piJ i) = i := by revert i; decide

@[expose] def Jm : Matrix (Fin 4) (Fin 4) F4 := Matrix.of fun i j => if j = piJ i then 1 else 0

theorem Jm_mul_Jm : Jm * Jm = 1 := f4mat_ext (by decide)

theorem coe_SL4_mul (g h : SL4) :
    ((g * h : SL4) : Matrix (Fin 4) (Fin 4) F4) =
      (g : Matrix (Fin 4) (Fin 4) F4) * (h : Matrix (Fin 4) (Fin 4) F4) := rfl

theorem coe_SL4_one : ((1 : SL4) : Matrix (Fin 4) (Fin 4) F4) = 1 := rfl

theorem det_SL4 (g : SL4) : (g : Matrix (Fin 4) (Fin 4) F4).det = 1 := g.2

@[expose] def sigmaM (g : SL4) : Matrix (Fin 4) (Fin 4) F4 :=
  Jm * (((g⁻¹ : SL4) : Matrix (Fin 4) (Fin 4) F4)ᵀ.map frobF4) * Jm

theorem det_sigmaM (g : SL4) : (sigmaM g).det = 1 := by
  have hJ : Jm.det * Jm.det = 1 := by rw [← det_mul, Jm_mul_Jm, det_one]
  have hmap : ((((g⁻¹ : SL4) : Matrix (Fin 4) (Fin 4) F4)ᵀ).map frobF4).det = 1 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, det_transpose, det_SL4, map_one]
  rw [sigmaM, det_mul, det_mul, hmap, mul_one, hJ]

theorem Jm_conj_mul (X Y : Matrix (Fin 4) (Fin 4) F4) :
    Jm * (X * Y) * Jm = (Jm * X * Jm) * (Jm * Y * Jm) := by
  calc Jm * (X * Y) * Jm = Jm * X * (Jm * Jm) * Y * Jm := by
        rw [Jm_mul_Jm, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = (Jm * X * Jm) * (Jm * Y * Jm) := by simp only [Matrix.mul_assoc]

theorem sigmaM_mul (g h : SL4) : sigmaM (g * h) = sigmaM g * sigmaM h := by
  have e1 : (((g * h)⁻¹ : SL4) : Matrix (Fin 4) (Fin 4) F4) =
      ((h⁻¹ : SL4) : Matrix (Fin 4) (Fin 4) F4) * ((g⁻¹ : SL4) : Matrix (Fin 4) (Fin 4) F4) := by
    rw [_root_.mul_inv_rev, coe_SL4_mul]
  rw [sigmaM, e1, transpose_mul, Matrix.map_mul, Jm_conj_mul]
  rfl

theorem sigmaM_one : sigmaM 1 = 1 := by
  rw [sigmaM, inv_one, coe_SL4_one, transpose_one,
    Matrix.map_one _ (map_zero frobF4) (map_one frobF4), Matrix.mul_one, Jm_mul_Jm]

@[expose] noncomputable def sigmaSL : SL4 →* SL4 where
  toFun g := ⟨sigmaM g, det_sigmaM g⟩
  map_one' := Subtype.ext sigmaM_one
  map_mul' g h := Subtype.ext (sigmaM_mul g h)

theorem mF4_eq_reBit (α : F4) (β γ : Fin 2) : mF4 α β γ = bz (reBit α.code β γ) := by
  have key : ∀ (α : F4) (β γ : Fin 2), decide (mF4 α β γ = bz (reBit α.code β γ)) = true := by
    decide
  exact of_decide_eq_true (key α β γ)

theorem toMat_reBits (M : Matrix (Fin 4) (Fin 4) F4) :
    toMat 8 8 (reBits fun i j => (M i j).code) = reF4 M := by
  ext r c
  obtain ⟨⟨i, β⟩, rfl⟩ := (finProdFinEquiv (m := 4) (n := 2)).surjective r
  obtain ⟨⟨j, γ⟩, rfl⟩ := (finProdFinEquiv (m := 4) (n := 2)).surjective c
  rw [reF4_apply, mF4_eq_reBit, toMat_apply, reBits, getD_ofFn, testBit_bitsOf]
  simp only [finProdFinEquiv, Equiv.coe_fn_mk]
  have h1 : ((γ : ℕ) + 2 * (j : ℕ)) < 8 := by omega
  have h2 : ((β : ℕ) + 2 * (i : ℕ)) / 2 = i := by omega
  have h3 : ((β : ℕ) + 2 * (i : ℕ)) % 2 = β := by omega
  have h4 : ((γ : ℕ) + 2 * (j : ℕ)) / 2 = j := by omega
  have h5 : ((γ : ℕ) + 2 * (j : ℕ)) % 2 = γ := by omega
  have hi : (⟨((β : ℕ) + 2 * (i : ℕ)) / 2, by omega⟩ : Fin 4) = i := Fin.ext h2
  have hj : Fin.ofNat 4 (((γ : ℕ) + 2 * (j : ℕ)) / 2) = j := Fin.ext (by simp [Fin.ofNat, h4])
  simp only [h1, decide_true, Bool.true_and, hi, hj, h3, h5]

@[expose] def bdiag (A B : Mat8) : Mat16 :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B)

theorem bdiag_mul (A B A' B' : Mat8) : bdiag A B * bdiag A' B' = bdiag (A * A') (B * B') := by
  simp only [bdiag, Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem bdiag_one : bdiag 1 1 = 1 := by
  rw [bdiag, Matrix.fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

theorem bdiag_injective_left {A B A' B' : Mat8} (h : bdiag A B = bdiag A' B') : A = A' := by
  ext i j
  have := congrFun (congrFun h (Fin.castAdd 8 i)) (Fin.castAdd 8 j)
  simpa only [bdiag, Matrix.reindex_apply, Matrix.submatrix_apply,
    finSumFinEquiv_symm_apply_castAdd, fromBlocks_apply₁₁] using this

theorem bdiag_injective_right {A B A' B' : Mat8} (h : bdiag A B = bdiag A' B') : B = B' := by
  ext i j
  have := congrFun (congrFun h (Fin.natAdd 8 i)) (Fin.natAdd 8 j)
  simpa only [bdiag, Matrix.reindex_apply, Matrix.submatrix_apply,
    finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₂₂] using this

theorem bdiag_cc (A B : Mat8) (i j : Fin 8) : bdiag A B (Fin.castAdd 8 i) (Fin.castAdd 8 j) = A i j := by
  simp only [bdiag, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
    fromBlocks_apply₁₁]

theorem bdiag_cn (A B : Mat8) (i j : Fin 8) : bdiag A B (Fin.castAdd 8 i) (Fin.natAdd 8 j) = 0 := by
  simp only [bdiag, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₁₂, Matrix.zero_apply]

theorem bdiag_nc (A B : Mat8) (i j : Fin 8) : bdiag A B (Fin.natAdd 8 i) (Fin.castAdd 8 j) = 0 := by
  simp only [bdiag, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₂₁, Matrix.zero_apply]

theorem bdiag_nn (A B : Mat8) (i j : Fin 8) : bdiag A B (Fin.natAdd 8 i) (Fin.natAdd 8 j) = B i j := by
  simp only [bdiag, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
    fromBlocks_apply₂₂]

theorem testBit_mod256_lo (a j : ℕ) (hj : j < 8) : (a % 256).testBit j = a.testBit j := by
  rw [show (256 : ℕ) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow]
  simp [hj]

theorem testBit_mod256_hi (a j : ℕ) : (a % 256).testBit (j + 8) = false := by
  apply Nat.testBit_eq_false_of_lt
  calc a % 256 < 256 := Nat.mod_lt _ (by norm_num)
    _ ≤ 2 ^ (j + 8) := by
      rw [pow_add]; exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos j)

theorem toMat_bdiagBits (A B : Array ℕ) :
    toMat 16 16 (bdiagBits A B) = bdiag (toMat 8 8 A) (toMat 8 8 B) := by
  ext r c
  refine Fin.addCases (m := 8) (n := 8) (fun i => ?_) (fun i => ?_) r <;>
    refine Fin.addCases (m := 8) (n := 8) (fun j => ?_) (fun j => ?_) c
  · rw [bdiag_cc, toMat_apply, toMat_apply, bdiagBits, getD_ofFn]
    simp [testBit_mod256_lo _ _ j.isLt]
  · rw [bdiag_cn, toMat_apply, bdiagBits, getD_ofFn]
    simp [testBit_mod256_hi]
  · rw [bdiag_nc, toMat_apply, bdiagBits, getD_ofFn]
    have : ¬ (8 ≤ (j : ℕ)) := by omega
    simp [Nat.testBit_shiftLeft, this]
  · rw [bdiag_nn, toMat_apply, toMat_apply, bdiagBits, getD_ofFn]
    simp [Nat.testBit_shiftLeft, testBit_mod256_lo _ _ j.isLt]

@[expose] def lineM (z : ℕ) : Mat16 := toMat 16 16 (lineBits z)

@[expose] def lineInvM (z : ℕ) : Mat16 := toMat 16 16 (lineInvBits z)

theorem lineM_mul_lineInvM (z : ℕ) : lineM z * lineInvM z = 1 := by
  rw [lineM, lineInvM, ← toMat_bmul]
  apply toMat_eq_one_of_bIsId
  by_cases hz : z < 2 <;> simp only [lineBits, lineInvBits, hz, ↓reduceIte] <;> decide

theorem lineInvM_mul_lineM (z : ℕ) : lineInvM z * lineM z = 1 := by
  rw [lineM, lineInvM, ← toMat_bmul]
  apply toMat_eq_one_of_bIsId
  by_cases hz : z < 2 <;> simp only [lineBits, lineInvBits, hz, ↓reduceIte] <;> decide

@[expose] noncomputable def rhoL (z : ℕ) : SL4 →* Mat16 where
  toFun g := lineM z * bdiag (reF4 (g : Matrix (Fin 4) (Fin 4) F4))
    (reF4 ((sigmaSL g : SL4) : Matrix (Fin 4) (Fin 4) F4)) * lineInvM z
  map_one' := by
    simp only [map_one, coe_SL4_one, bdiag_one, Matrix.mul_one, lineM_mul_lineInvM]
  map_mul' g h := by
    simp only [map_mul, coe_SL4_mul]
    rw [← bdiag_mul]
    calc lineM z * (bdiag (reF4 ↑g) (reF4 ↑(sigmaSL g)) * bdiag (reF4 ↑h) (reF4 ↑(sigmaSL h))) *
          lineInvM z
        = lineM z * bdiag (reF4 ↑g) (reF4 ↑(sigmaSL g)) * (lineInvM z * lineM z) *
            bdiag (reF4 ↑h) (reF4 ↑(sigmaSL h)) * lineInvM z := by
          rw [lineInvM_mul_lineM, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem rhoL_apply (z : ℕ) (g : SL4) :
    rhoL z g = lineM z * bdiag (reF4 (g : Matrix (Fin 4) (Fin 4) F4))
      (reF4 ((sigmaSL g : SL4) : Matrix (Fin 4) (Fin 4) F4)) * lineInvM z := rfl

theorem rhoL_injective (z : ℕ) : Function.Injective (rhoL z) := by
  intro g h hgh
  have h1 : bdiag (reF4 (g : Matrix (Fin 4) (Fin 4) F4))
      (reF4 ((sigmaSL g : SL4) : Matrix (Fin 4) (Fin 4) F4)) =
      bdiag (reF4 (h : Matrix (Fin 4) (Fin 4) F4))
      (reF4 ((sigmaSL h : SL4) : Matrix (Fin 4) (Fin 4) F4)) := by
    have := congrArg (fun X => lineInvM z * X * lineM z) hgh
    simp only [rhoL_apply, ← Matrix.mul_assoc, lineInvM_mul_lineM, Matrix.one_mul] at this
    simpa only [Matrix.mul_assoc, lineInvM_mul_lineM, Matrix.mul_one] using this
  exact Subtype.ext (reF4_injective (bdiag_injective_left h1))

noncomputable abbrev st4 (a b : Fin 4) (c : F4) : SL4 := stT (F := F4) (m := 3) (by norm_num) a b c

theorem coe_st4 {a b : Fin 4} (hab : a ≠ b) (c : F4) :
    ((st4 a b c : SL4) : Matrix (Fin 4) (Fin 4) F4) = Matrix.transvection a b c := by
  rw [st4, stT_eq_transvection _ hab]
  rfl

theorem st4_inv (a b : Fin 4) (c : F4) : (st4 a b c)⁻¹ = st4 a b c :=
  inv_eq_of_mul_eq_one_right (stT_mul_self _ a b c)

theorem sigma_transvection_matrix (a b : Fin 4) (hab : a ≠ b) (c : F4) :
    Jm * ((Matrix.transvection a b c)ᵀ.map frobF4) * Jm =
      Matrix.transvection (piJ b) (piJ a) (frobF4 c) := by
  have key : ∀ (a b : Fin 4) (c : F4) (i j : Fin 4), decide (a ≠ b →
      ((Jm * ((Matrix.transvection a b c)ᵀ.map frobF4) * Jm) i j).code =
        (Matrix.transvection (piJ b) (piJ a) (frobF4 c) i j).code) = true := by
    decide
  exact f4mat_ext fun i j => of_decide_eq_true (key a b c i j) hab

theorem piJ_ne {a b : Fin 4} (hab : a ≠ b) : piJ b ≠ piJ a := fun h =>
  hab (by have := congrArg piJ h; rw [piJ_piJ, piJ_piJ] at this; exact this.symm)

theorem sigmaSL_st4 (a b : Fin 4) (c : F4) :
    sigmaSL (st4 a b c) = st4 (piJ b) (piJ a) (frobF4 c) := by
  by_cases hab : a = b
  · subst hab
    rw [st4, st4, stT_diag, stT_diag, map_one]
  · apply Subtype.ext
    change sigmaM (st4 a b c) = _
    rw [coe_st4 (piJ_ne hab), sigmaM, st4_inv, coe_st4 hab, sigma_transvection_matrix a b hab]

theorem code_transvection {a b : Fin 4} (hab : a ≠ b) (c : F4) (i j : Fin 4) :
    ((Matrix.transvection a b c i j).code : ℕ) = trCode a b c.code i j := by
  have key : ∀ (a b : Fin 4) (c : F4) (i j : Fin 4), decide (a ≠ b →
      ((Matrix.transvection a b c i j).code : ℕ) = trCode a b c.code i j) = true := by
    decide
  exact of_decide_eq_true (key a b c i j) hab

theorem code_frobF4 (c : F4) : ((frobF4 c).code : ℕ) = frobCode c.code := by
  have key : ∀ c : F4, decide (((frobF4 c).code : ℕ) = frobCode c.code) = true := by decide
  exact of_decide_eq_true (key c)

theorem toMat_lineConjBits (z : ℕ) (A B : Array ℕ) :
    toMat 16 16 (lineConjBits z A B) = lineM z * bdiag (toMat 8 8 A) (toMat 8 8 B) * lineInvM z := by
  rw [lineConjBits, toMat_bmul, toMat_bmul, toMat_bdiagBits, lineM, lineInvM]

theorem reF4_transvection {a b : Fin 4} (hab : a ≠ b) (c : F4) :
    reF4 (Matrix.transvection a b c) = toMat 8 8 (reBits (trCode a b c.code)) := by
  rw [← toMat_reBits]
  congr 2
  funext i j
  exact code_transvection hab c i j

theorem rhoL_st4 (z : ℕ) {a b : Fin 4} (hab : a ≠ b) (c : F4) :
    rhoL z (st4 a b c) = toMat 16 16 (rhoTrBits z a b c.code) := by
  rw [rhoL_apply, sigmaSL_st4, coe_st4 hab, coe_st4 (piJ_ne hab), reF4_transvection hab,
    reF4_transvection (piJ_ne hab), code_frobF4, rhoTrBits, toMat_lineConjBits]

end CFSG.EvenSmallLie.UnitarySix.YamadaPar
