module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOrthNormal
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLGraph

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Gr

open CFSG Subgroup Matrix
open CFSG.ComponentClassification.Burgoyne.PSL

variable {n : ℕ} {K : Type} [Field K]

theorem permMatrixHom_transpose (σ : Equiv.Perm (Fin n)) :
    (Matrix.permMatrixHom (R := K) σ)ᵀ = Matrix.permMatrixHom (R := K) σ⁻¹ := by
  rw [Matrix.permMatrixHom_apply, Matrix.permMatrixHom_apply, Matrix.transpose_permMatrix]

theorem permMatrixHom_diagonal (σ : Equiv.Perm (Fin n)) (d : Fin n → K) :
    Matrix.permMatrixHom (R := K) σ * diagonal d * (Matrix.permMatrixHom (R := K) σ)ᵀ =
      diagonal fun x => d (σ⁻¹ x) := by
  rw [permMatrixHom_transpose, Matrix.permMatrixHom_apply, Matrix.permMatrixHom_apply, inv_inv,
    Equiv.Perm.permMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix]
  ext a b
  simp only [submatrix_apply, Function.comp_apply, id, diagonal_apply]
  have e : (σ.symm : Fin n → Fin n) = (σ⁻¹ : Equiv.Perm (Fin n)) := rfl
  rw [e]
  simp only [(σ⁻¹ : Equiv.Perm (Fin n)).injective.eq_iff]

@[expose] def permSL (σ : Equiv.Perm (Fin n)) (hσ : Equiv.Perm.sign σ = 1) :
    Matrix.SpecialLinearGroup (Fin n) K :=
  ⟨Matrix.permMatrixHom (R := K) σ, by
    rw [Matrix.permMatrixHom_apply, Matrix.det_permutation, Equiv.Perm.sign_inv, hσ]
    simp⟩

theorem coe_permSL (σ : Equiv.Perm (Fin n)) (hσ : Equiv.Perm.sign σ = 1) :
    ((permSL σ hσ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.permMatrixHom (R := K) σ := rfl

theorem permSL_inv (σ : Equiv.Perm (Fin n)) (hσ : Equiv.Perm.sign σ = 1) :
    (permSL (K := K) σ hσ)⁻¹ = permSL σ⁻¹ (by rw [Equiv.Perm.sign_inv, hσ]) := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_permSL, coe_permSL, ← map_mul, mul_inv_cancel,
    map_one, Matrix.SpecialLinearGroup.coe_one]

theorem permSL_pow_eq_one (σ : Equiv.Perm (Fin n)) (hσ : Equiv.Perm.sign σ = 1) {k : ℕ}
    (hk : σ ^ k = 1) : permSL (K := K) σ hσ ^ k = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_permSL, ← map_pow, hk, map_one,
    Matrix.SpecialLinearGroup.coe_one]

theorem permSL_mem_isometry {w : Fin n → K} (hw : ∀ i, w i ≠ 0) (σ : Equiv.Perm (Fin n))
    (hσ : Equiv.Perm.sign σ = 1) (hwσ : ∀ x, w (σ x) = w x) :
    permSL (K := K) σ hσ ∈ isometrySL n (diagGL hw) := by
  rw [mem_comap, CatalogueBGraphForm.mem_isometryGroup]
  change (Matrix.permMatrixHom (R := K) σ)ᵀ * (diagGL hw : Matrix (Fin n) (Fin n) K) *
    Matrix.permMatrixHom (R := K) σ = (diagGL hw : Matrix (Fin n) (Fin n) K)
  have hP : Matrix.permMatrixHom (R := K) σ = (Matrix.permMatrixHom (R := K) σ⁻¹)ᵀ := by
    rw [permMatrixHom_transpose, inv_inv]
  rw [permMatrixHom_transpose, hP, coe_diagGL, permMatrixHom_diagonal]
  congr 1
  ext x
  exact hwσ x

@[expose] noncomputable def signPair {i j : Fin n} (hij : i ≠ j) :
    Matrix.SpecialLinearGroup (Fin n) K :=
  signSL K {i, j} (by rw [Finset.card_pair hij]; exact even_two)

theorem coe_signPair {i j : Fin n} (hij : i ≠ j) :
    ((signPair (K := K) hij : Matrix.SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = signMat K {i, j} := rfl

theorem signPair_mul_self {i j : Fin n} (hij : i ≠ j) :
    signPair (K := K) hij * signPair hij = 1 := signSL_mul_self _ _

theorem signPair_inv {i j : Fin n} (hij : i ≠ j) :
    (signPair (K := K) hij)⁻¹ = signPair hij :=
  inv_eq_of_mul_eq_one_right (signPair_mul_self hij)

theorem signPair_eq {i j i' j' : Fin n} (hij : i ≠ j) (h' : i' ≠ j') (hi : i = i') (hj : j = j') :
    signPair (K := K) hij = signPair h' := by
  subst hi
  subst hj
  rfl

theorem signPair_comm {i j : Fin n} (hij : i ≠ j) : signPair (K := K) hij = signPair hij.symm :=
  Subtype.ext (by rw [coe_signPair, coe_signPair, Finset.pair_comm])

theorem signPair_mem_isometry {w : Fin n → K} (hw : ∀ i, w i ≠ 0) {i j : Fin n} (hij : i ≠ j) :
    signPair (K := K) hij ∈ isometrySL n (diagGL hw) := by
  rw [mem_comap, CatalogueBGraphForm.mem_isometryGroup]
  change (signMat K {i, j})ᵀ * (diagGL hw : Matrix (Fin n) (Fin n) K) * signMat K {i, j} =
    (diagGL hw : Matrix (Fin n) (Fin n) K)
  rw [coe_diagGL, signMat, diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  ext k
  split_ifs <;> ring

theorem conj_signSL_pair (σ : Equiv.Perm (Fin n)) (hσ : Equiv.Perm.sign σ = 1) {i j : Fin n}
    (hij : i ≠ j) :
    permSL (K := K) σ hσ * signPair hij * (permSL σ hσ)⁻¹ =
      signPair (σ.injective.ne hij) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, permSL_inv,
    coe_permSL, coe_permSL, coe_signPair, coe_signPair, ← permMatrixHom_transpose, signMat,
    permMatrixHom_diagonal, signMat]
  congr 1
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton, Equiv.Perm.inv_eq_iff_eq]

theorem signPair_mul {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    signPair (K := K) hab * signPair hbc = signPair hac := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_signPair, coe_signPair, coe_signPair, signMat,
    signMat, signMat, diagonal_mul_diagonal]
  congr 1
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  by_cases hxa : x = a
  · subst hxa
    simp [hab, hac]
  · by_cases hxb : x = b
    · subst hxb
      simp [hxa, hbc]
    · by_cases hxc : x = c
      · subst hxc
        simp [hxa, hxb]
      · simp [hxa, hxb, hxc]

theorem exists_three_cycle {a b d : Fin n} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    ∃ c : Equiv.Perm (Fin n), Equiv.Perm.sign c = 1 ∧ c ^ 3 = 1 ∧ c a = b ∧ c b = d ∧
      c d = a ∧ ∀ x, x ≠ a → x ≠ b → x ≠ d → c x = x := by
  have h3 : (Equiv.swap b a * Equiv.swap b d).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same (Ne.symm hab) hbd had
  refine ⟨Equiv.swap b a * Equiv.swap b d, h3.sign, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h3.orderOf]
    exact pow_orderOf_eq_one _
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hab had, Equiv.swap_apply_right]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hbd.symm
      (Ne.symm had)]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]
  · intro x hxa hxb hxd
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxb hxd,
      Equiv.swap_apply_of_ne_of_ne hxb hxa]

end CFSG.ComponentClassification.Foote5.OddLieCore.Gr
