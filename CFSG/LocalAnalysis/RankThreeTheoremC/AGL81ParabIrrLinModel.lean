module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinModel
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.Lin

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.AGLEmbedding.LeviBlock
  CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin

section Block

variable {K : Type} [Field K] {n : ℕ} {I : Set ℕ}

theorem exists_pow_two_eq_one_of_blocks [Finite K] [CharP K 2] (hn : 1 ≤ n) {D : GL (Fin n) K}
    (hD : BlockPat I (D : Matrix (Fin n) (Fin n) K))
    (hdet : (D : Matrix (Fin n) (Fin n) K).det = 1)
    (hblk : ∀ a : Fin n, blkAt a (linBlockLen n I a) (linBlockLen_le a)
      (D : Matrix (Fin n) (Fin n) K) = 1) :
    ∃ k : ℕ, (conjAut n K D) ^ 2 ^ k = 1 := by
  let g : SpecialLinearGroup (Fin n) K := ⟨(D : Matrix (Fin n) (Fin n) K), hdet⟩
  have hgQ : g ∈ flagStabilizer n K I := mem_flagStabilizer_of_blockPat hD
  have hker : (⟨g, hgQ⟩ : flagStabilizer n K I) ∈ (linLeviHom K n I).ker := by
    rw [MonoidHom.mem_ker]
    funext a
    apply Units.ext
    rw [coe_linLeviHom_apply, Pi.one_apply, Units.val_one]
    exact hblk a
  obtain ⟨k, hk⟩ := isPGroup_ker_linLeviHom (K := K) (n := n) (I := I) hn ⟨_, hker⟩
  refine ⟨k, ?_⟩
  have hgpow : g ^ 2 ^ k = 1 := by
    have h1 := congrArg (fun y : (linLeviHom K n I).ker =>
      ((y : flagStabilizer n K I) : SpecialLinearGroup (Fin n) K)) hk
    simpa using h1
  have hCg : (SpecialLinearGroup.toGL g : GL (Fin n) K) = D := Units.ext rfl
  rw [← hCg, conjAut_toGL, ← map_pow, ← map_pow, hgpow, map_one, map_one]

theorem blockPat_pow {M : Matrix (Fin n) (Fin n) K} (hM : BlockPat I M) (j : ℕ) :
    BlockPat I (M ^ j) := by
  induction j with
  | zero => rw [pow_zero]; exact BlockPat.one
  | succ j ih => rw [pow_succ]; exact ih.mul hM

theorem blkAt_pow_of_blockPat {a m : ℕ} (h : a + m ≤ n) (ha : a = 0 ∨ a ∈ I)
    (hb : a + m = n ∨ a + m ∈ I) {M : Matrix (Fin n) (Fin n) K} (hM : BlockPat I M) (j : ℕ) :
    blkAt a m h (M ^ j) = blkAt a m h M ^ j := by
  induction j with
  | zero => rw [pow_zero, pow_zero, blkAt_one]
  | succ j ih =>
    rw [pow_succ, pow_succ, blkAt_mul_of_blockPat h ha hb (blockPat_pow hM j) hM, ih]

theorem val_glMap_eq_map (σ : K →+* K) (A : GL (Fin n) K) :
    ((GeneralLinearGroup.map σ A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (A : Matrix (Fin n) (Fin n) K).map σ := rfl

theorem blkAt_conj_field {C' A : GL (Fin n) K} {σ : K ≃+* K} {k : ℕ}
    (hσ : ∀ a, σ a = a ^ 2 ^ k)
    (hC : BlockPat I (C' : Matrix (Fin n) (Fin n) K))
    (hC' : BlockPat I ((C'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hA : BlockPat I (A : Matrix (Fin n) (Fin n) K))
    (hA' : BlockPat I ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hsc : ScalarBlocks I (A : Matrix (Fin n) (Fin n) K)) (a : Fin n) :
    blkAt a (linBlockLen n I a) (linBlockLen_le a)
      ((C' * GeneralLinearGroup.map (σ : K →+* K) A * C'⁻¹ * (A⁻¹) ^ 2 ^ k : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = 1 := by
  by_cases hstart : (a : ℕ) = 0 ∨ (a : ℕ) ∈ I
  swap
  · exact matrix_eq_of_eq_zero (linBlockLen_of_not_start hstart) _ _
  obtain ⟨-, hm1, hend, -⟩ := linBlockLen_spec (I := I) hstart
  have hle := linBlockLen_le (n := n) (I := I) a
  obtain ⟨r, hr⟩ := hsc a
  have hi : blkAt a (linBlockLen n I a) hle ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (r • 1) = 1 := by
    rw [← hr, ← blkAt_mul_of_blockPat hle hstart hend hA' hA, Units.inv_mul, blkAt_one]
  obtain ⟨hr0, hAi⟩ := eq_inv_smul_one_of_mul hm1 hi
  have hCC : blkAt a (linBlockLen n I a) hle (C' : Matrix (Fin n) (Fin n) K) *
      blkAt a (linBlockLen n I a) hle ((C'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← blkAt_mul_of_blockPat hle hstart hend hC hC', Units.mul_inv, blkAt_one]
  have hAσ : BlockPat I ((GeneralLinearGroup.map (σ : K →+* K) A : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) := by
    rw [val_glMap_eq_map]
    exact hA.map _
  have hAσblk : blkAt a (linBlockLen n I a) hle
      ((GeneralLinearGroup.map (σ : K →+* K) A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        σ r • 1 := by
    rw [val_glMap_eq_map, blkAt_map, hr]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hP : BlockPat I (((A⁻¹ ^ 2 ^ k : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) := by
    rw [Units.val_pow_eq_pow_val]
    exact blockPat_pow hA' _
  have h1 : blkAt a (linBlockLen n I a) hle (C' : Matrix (Fin n) (Fin n) K) * (σ r • 1) *
      blkAt a (linBlockLen n I a) hle ((C'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        σ r • 1 := by
    rw [Matrix.mul_smul, mul_one, Matrix.smul_mul, hCC]
  simp only [Units.val_mul]
  rw [blkAt_mul_of_blockPat hle hstart hend ((hC.mul hAσ).mul hC') hP,
    blkAt_mul_of_blockPat hle hstart hend (hC.mul hAσ) hC',
    blkAt_mul_of_blockPat hle hstart hend hC hAσ, Units.val_pow_eq_pow_val,
    blkAt_pow_of_blockPat hle hstart hend hA', hAi, hAσblk, h1, smul_pow, one_pow]
  calc (σ r • (1 : Matrix (Fin (linBlockLen n I a)) (Fin (linBlockLen n I a)) K)) *
        (r⁻¹ ^ 2 ^ k • 1)
      = (σ r * r⁻¹ ^ 2 ^ k) • (1 : Matrix (Fin (linBlockLen n I a))
          (Fin (linBlockLen n I a)) K) := by
        rw [Matrix.smul_mul, one_mul, smul_smul]
    _ = 1 := by rw [hσ r, ← mul_pow, mul_inv_cancel₀ hr0, one_pow, one_smul]

theorem det_conj_field {C' A : GL (Fin n) K} {σ : K ≃+* K} {k : ℕ} (hσ : ∀ a, σ a = a ^ 2 ^ k) :
    ((C' * GeneralLinearGroup.map (σ : K →+* K) A * C'⁻¹ * (A⁻¹) ^ 2 ^ k : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K).det = 1 := by
  have h : GeneralLinearGroup.det
      (C' * GeneralLinearGroup.map (σ : K →+* K) A * C'⁻¹ * (A⁻¹) ^ 2 ^ k) = 1 := by
    have h1 : GeneralLinearGroup.det (GeneralLinearGroup.map (σ : K →+* K) A) =
        GeneralLinearGroup.det A ^ 2 ^ k := by
      rw [GeneralLinearGroup.map_det]
      exact Units.ext (hσ _)
    simp only [map_mul, map_inv, map_pow, h1]
    rw [mul_right_comm (GeneralLinearGroup.det C'), mul_inv_cancel, one_mul, ← mul_pow,
      mul_inv_cancel, one_pow]
  have := congrArg Units.val h
  rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at this

end Block

section Model

variable {K : Type} [Field K] {n : ℕ} {I : Set ℕ}

theorem exists_pow_two_eq_one_conj_field [Finite K] [CharP K 2] (hn : 1 ≤ n)
    (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n) {C' A : GL (Fin n) K} {σ : K ≃+* K} {k : ℕ}
    (hσ : ∀ a, σ a = a ^ 2 ^ k)
    (hflag : (projFlag K n I).map (conjAut n K C' * fieldAut n K σ).toMonoidHom = projFlag K n I)
    (hA : BlockPat I (A : Matrix (Fin n) (Fin n) K))
    (hA' : BlockPat I ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hsc : ScalarBlocks I (A : Matrix (Fin n) (Fin n) K)) :
    ∃ j : ℕ, ((conjAut n K C' * fieldAut n K σ) * conjAut n K A *
      (conjAut n K C' * fieldAut n K σ)⁻¹ * (conjAut n K A ^ 2 ^ k)⁻¹) ^ 2 ^ j = 1 := by
  obtain ⟨hC', hC⟩ := blockPat_of_conj_mem hI C' (conj_mem_of_map_projFlag hflag)
  have htrans := standard_automorphism_transport (K := K) (n := n)
  have hX : (conjAut n K C' * fieldAut n K σ) * conjAut n K A *
      (conjAut n K C' * fieldAut n K σ)⁻¹ * (conjAut n K A ^ 2 ^ k)⁻¹ =
      conjAut n K (C' * GeneralLinearGroup.map (σ : K →+* K) A * C'⁻¹ * (A⁻¹) ^ 2 ^ k) := by
    have h1 : (conjAut n K C' * fieldAut n K σ) * conjAut n K A *
        (conjAut n K C' * fieldAut n K σ)⁻¹ * (conjAut n K A ^ 2 ^ k)⁻¹ =
        conjAut n K C' * (fieldAut n K σ * conjAut n K A * (fieldAut n K σ)⁻¹) *
          (conjAut n K C')⁻¹ * (conjAut n K A ^ 2 ^ k)⁻¹ := by
      generalize conjAut n K A ^ 2 ^ k = z
      group
    rw [h1, htrans.2.2.1]
    simp only [map_mul, map_inv, map_pow, inv_pow]
  have hDpat : BlockPat I ((C' * GeneralLinearGroup.map (σ : K →+* K) A * C'⁻¹ * (A⁻¹) ^ 2 ^ k :
      GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, val_glMap_eq_map]
    exact ((hC.mul (hA.map _)).mul hC').mul (blockPat_pow hA' _)
  obtain ⟨j, hj⟩ := exists_pow_two_eq_one_of_blocks hn hDpat (det_conj_field hσ)
    (blkAt_conj_field hσ hC hC' hA hA' hsc)
  exact ⟨j, by rw [hX]; exact hj⟩

end Model

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.Lin
