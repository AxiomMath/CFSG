module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUf

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut StabU DiagU ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank LinearFlag
  CFSG.ComponentClassification.CatalogueBUnitaryB CFSG.LinearGroups
  CFSG.ComponentClassification.OddSelector
  CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

section Field

variable {k : Type} [Field k]

@[expose] def mU0 : Matrix (Fin 4) (Fin 4) k :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1]

theorem mU0_mulVec (x : Fin 4 → k) : (mU0 : Matrix (Fin 4) (Fin 4) k) *ᵥ x =
    ![x 1, x 0, -x 2, x 3] := by
  funext i
  fin_cases i
  all_goals simp [mU0, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem mU0_transpose : (mU0 : Matrix (Fin 4) (Fin 4) k)ᵀ = mU0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mU0]

theorem mU0_mul_self : (mU0 : Matrix (Fin 4) (Fin 4) k) * mU0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mU0, Matrix.mul_apply, Fin.sum_univ_four]

theorem map_mU0 {K : Type} [Field K] (ι : k →+* K) :
    (mU0 : Matrix (Fin 4) (Fin 4) k).map ι = mU0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mU0]

theorem Umat_g0 (δ : kˣ) (h2 : (2 : k) ≠ 0) :
    (Umat δ h2 (OIL.g0 (δ : k)) : Matrix (Fin 4) (Fin 4) k) = mU0 :=
  Matrix.toLin'.injective (LinearMap.ext fun x => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Umat_mulVec, OIL.coord_g0, mU0_mulVec])

theorem mD_mul_mU0 (a b h : k) : OIL.mD a b h * mU0 = OIL.mD (-a) (-b) h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [OIL.mD, mU0, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.zero_eta,
      Fin.mk_one] <;> ring

theorem dotProduct_gramQ' (δ : k) (x y : Fin 4 → k) :
    x ⬝ᵥ (gramQ δ *ᵥ y) = OIL.qf δ (x + y) - OIL.qf δ x - OIL.qf δ y := by
  simp only [gramQ, OIL.qf, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.add_apply]
  simp
  ring

theorem mDT_gram_mD (δ : k) {a b h : k} (hab : a ^ 2 + b ^ 2 = -1) (hh : 2 * h = 1) :
    (OIL.mD a b h)ᵀ * gramQ δ * OIL.mD a b h = mU0 * gramQ δ := by
  apply OIL.eq_of_dotProduct_mulVec
  intro x y
  rw [Matrix.mul_assoc, OIL.dotProduct_transpose_mul, ← Matrix.mulVec_mulVec,
    dotProduct_gramQ' δ, OIL.qf_polar_mD δ hab hh, ← mU0_transpose,
    OIL.dotProduct_transpose_mul, dotProduct_gramQ' δ, mU0_mulVec]

end Field

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem fusion_matrix (hp2 : p ≠ 2) (δ : K) {j a₀ b₀ : K} (hj : h.bar j = -j)
    (ha₀ : h.bar a₀ = a₀) (hb₀ : h.bar b₀ = b₀) (hab : (a₀ ^ 2 + b₀ ^ 2) * j ^ 2 = -1) :
    (OIL.mD (a₀ * j) (b₀ * j) 2⁻¹).map h.bar = OIL.mD (a₀ * j) (b₀ * j) 2⁻¹ * mU0 ∧
      ((OIL.mD (a₀ * j) (b₀ * j) 2⁻¹).map h.bar)ᵀ * gramQ δ * OIL.mD (a₀ * j) (b₀ * j) 2⁻¹ =
        gramQ δ ∧
      (OIL.mD (a₀ * j) (b₀ * j) 2⁻¹).det = 1 := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  have hh : 2 * (2 : K)⁻¹ = 1 := mul_inv_cancel₀ h2
  have hab' : (a₀ * j) ^ 2 + (b₀ * j) ^ 2 = -1 := by linear_combination hab
  have hbar : (OIL.mD (a₀ * j) (b₀ * j) 2⁻¹).map h.bar = OIL.mD (a₀ * j) (b₀ * j) 2⁻¹ * mU0 := by
    rw [mD_mul_mU0]
    have h2b : h.bar (2 : K)⁻¹ = (2 : K)⁻¹ := by rw [map_inv₀, map_ofNat]
    ext i j'
    fin_cases i <;> fin_cases j' <;>
      simp [OIL.mD, map_mul, map_add, map_sub, map_neg, ha₀, hb₀, hj, h2b]
  refine ⟨hbar, ?_, OIL.det_mD hab' hh⟩
  rw [hbar, Matrix.transpose_mul, mU0_transpose, Matrix.mul_assoc, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ (gramQ δ), mDT_gram_mD δ hab' hh, ← Matrix.mul_assoc, mU0_mul_self,
    Matrix.one_mul]

end OIU

end CFSG.ComponentClassification.CatFactsL4U4
