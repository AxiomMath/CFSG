module

public import CFSG.ClassicalInvolution.WeakCT.Blocks
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviSUThree
public import CFSG.RankThree.PartTwo.Sec15.ONanKS1424CoreDFT

public noncomputable section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.PauliWords

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalInvolution.WeakCT
  CFSG.AGLEmbedding CFSG.RankThree.PartTwo.Sec15.KS1424

open scoped MatrixGroups

variable {K : Type} [Field K] [CharP K 2]

@[expose] def diagonalWord (ζ : Kˣ) : SL(3, K) :=
  blockSL K 3 2 1 (by omega) (sl2Diag K ζ)

@[expose] def cycleWord : SL(3, K) :=
  blockSL K 3 2 0 (by omega) (sl2Weyl K 1) *
    blockSL K 3 2 1 (by omega) (sl2Weyl K 1)

@[expose] def centralWord (ζ : Kˣ) : SL(3, K) :=
  blockSL K 3 2 0 (by omega) (sl2Diag K ζ) *
    blockSL K 3 2 1 (by omega) (sl2Diag K (ζ ^ 2))

theorem centralWord_val (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    (centralWord ζ : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) (ζ : K) := by
  have hinv : ζ⁻¹ = ζ ^ 2 := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [← pow_succ] using hζ
  have hinv2 : (ζ ^ 2)⁻¹ = ζ := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [← pow_succ'] using hζ
  have h3 : (ζ : K) ^ 3 = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one]
      using congrArg (fun u : Kˣ => (u : K)) hζ
  have h4 : (ζ : K) ^ 4 = (ζ : K) := by rw [pow_succ, h3, one_mul]
  rw [centralWord, Matrix.SpecialLinearGroup.coe_mul,
    coe_blockSL_three_zero, coe_blockSL_three_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Diag, Matrix.scalar, Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_three,
      hinv, hinv2, ← pow_add, h4]

theorem centralWord_commute (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (A : SL(3, K)) :
    Commute (centralWord ζ) A := by
  change centralWord ζ * A = A * centralWord ζ
  apply Subtype.ext
  simpa only [Matrix.SpecialLinearGroup.coe_mul, centralWord_val ζ hζ]
    using (Matrix.scalar_commute (ζ : K) (fun r => Commute.all _ _) (A : Matrix (Fin 3) (Fin 3) K)).eq

theorem centralWord_pow_three (ζ : Kˣ) (hζ : ζ ^ 3 = 1) : centralWord ζ ^ 3 = 1 := by
  have h3 : (ζ : K) ^ 3 = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one]
      using congrArg (fun u : Kˣ => (u : K)) hζ
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, centralWord_val ζ hζ]
  change (Matrix.scalar (Fin 3) (ζ : K)) ^ 3 = 1
  rw [← map_pow, h3, map_one]

theorem diagonalWord_val (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    (diagonalWord ζ : Matrix (Fin 3) (Fin 3) K) = heisXMat (ζ : K) := by
  have hinv : ζ⁻¹ = ζ ^ 2 := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [← pow_succ] using hζ
  rw [diagonalWord, coe_blockSL_three_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Diag, heisXMat, hinv]

theorem cycleWord_val :
    (cycleWord (K := K) : Matrix (Fin 3) (Fin 3) K) = heisYMat := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hneg : (-1 : K) = 1 := by linear_combination -h2
  rw [cycleWord, Matrix.SpecialLinearGroup.coe_mul,
    coe_blockSL_three_zero, coe_blockSL_three_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Weyl, heisYMat, Matrix.mul_apply, Fin.sum_univ_three, hneg]

theorem cycleWord_pow_three : (cycleWord (K := K)) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, cycleWord_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisYMat, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def fourierWord (ζ : K) (hζ : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) : SL(3, K) :=
  ⟨fourierMatThree ζ, by
    change (dftMat ζ).det = 1
    exact det_dftMat hζ hζ1⟩

theorem fourierWord_val (ζ : K) (hζ : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) :
    (fourierWord ζ hζ hζ1 : Matrix (Fin 3) (Fin 3) K) = fourierMatThree ζ := rfl

theorem fourierWord_pow_four (ζ : K) (hζ : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) :
    (fourierWord ζ hζ hζ1) ^ 4 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, fourierWord_val]
  change dftMat ζ ^ 4 = 1
  exact dftMat_pow_four hζ hζ1

theorem fourierWord_conj_words (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (hζ1 : (ζ : K) ≠ 1) :
    let F := fourierWord (ζ : K)
      (by simpa only [Units.val_pow_eq_pow_val, Units.val_one]
        using congrArg (fun u : Kˣ => (u : K)) hζ) hζ1
    F * diagonalWord ζ * F⁻¹ = (cycleWord (K := K)) ^ 2 ∧
      F * cycleWord * F⁻¹ = diagonalWord ζ := by
  dsimp only
  have h3 : (ζ : K) ^ 3 = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one]
      using congrArg (fun u : Kˣ => (u : K)) hζ
  have hs : 1 + (ζ : K) + (ζ : K) ^ 2 = 0 := by
    have h : ((ζ : K) - 1) * (1 + (ζ : K) + (ζ : K) ^ 2) = 0 := by
      linear_combination h3
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hζ1)
  obtain ⟨hX, hY⟩ := fourier_conj_relations hs
  constructor
  · apply (mul_inv_eq_iff_eq_mul).2
    apply Subtype.ext
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow,
      fourierWord_val, diagonalWord_val ζ hζ, cycleWord_val, pow_two] using hX
  · apply (mul_inv_eq_iff_eq_mul).2
    apply Subtype.ext
    simpa only [Matrix.SpecialLinearGroup.coe_mul, fourierWord_val,
      diagonalWord_val ζ hζ, cycleWord_val] using hY

end CFSG.LieType.Chevalley.E7Three.PauliWords
