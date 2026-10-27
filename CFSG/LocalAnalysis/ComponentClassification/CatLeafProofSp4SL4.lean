module

public import CFSG.ClassicalInvolution.WeakCT.SpPair

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open Matrix CFSG.Timmesfeld CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock shortBlock longBlock_sl2Upper
  longBlock_sl2Lower shortBlock_sl2Upper shortBlock_sl2Lower)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_elt E)
open CFSG.Timmesfeld.LevisExtras (tv01_eq_sl2Upper tv10_eq_sl2Lower)
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def sp4Index : Fin 4 → Fin 2 ⊕ Fin 2 :=
  ![Sum.inl 0, Sum.inl 1, Sum.inr 1, Sum.inr 0]

theorem sp4Index_bijective : Function.Bijective sp4Index := by
  decide

@[expose] def sp4IndexEquiv : Fin 4 ≃ Fin 2 ⊕ Fin 2 :=
  Equiv.ofBijective sp4Index sp4Index_bijective

variable (F) in
@[expose] def sp4Sign : Fin 4 → F :=
  ![1, 1, 1, -1]

@[expose] def sp4Mat (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  diagonal (sp4Sign F) * X.submatrix sp4Index sp4Index * diagonal (sp4Sign F)

theorem sp4Mat_apply (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (k l : Fin 4) :
    sp4Mat X k l = sp4Sign F k * X (sp4Index k) (sp4Index l) * sp4Sign F l := by
  rw [sp4Mat, mul_diagonal, diagonal_mul, submatrix_apply]

theorem sp4Sign_mul_self (k : Fin 4) : sp4Sign F k * sp4Sign F k = 1 := by
  fin_cases k <;> simp [sp4Sign]

theorem diagonal_sp4Sign_mul_self : diagonal (sp4Sign F) * diagonal (sp4Sign F) = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext k
  exact sp4Sign_mul_self k

theorem sp4Mat_mul (X Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) :
    sp4Mat (X * Y) = sp4Mat X * sp4Mat Y := by
  have hsub : (X * Y).submatrix sp4Index sp4Index =
      X.submatrix sp4Index sp4Index * Y.submatrix sp4Index sp4Index :=
    (submatrix_mul_equiv X Y sp4Index sp4IndexEquiv sp4Index).symm
  rw [sp4Mat, sp4Mat, sp4Mat, hsub]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (diagonal (sp4Sign F)) (diagonal (sp4Sign F)),
    diagonal_sp4Sign_mul_self, Matrix.one_mul]

theorem sp4Mat_one : sp4Mat (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by
  have h1 : (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).submatrix sp4Index sp4Index = 1 :=
    submatrix_one_equiv sp4IndexEquiv
  rw [sp4Mat, h1, Matrix.mul_one, diagonal_sp4Sign_mul_self]

theorem det_sp4Mat (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) : (sp4Mat X).det = X.det := by
  have hD : (diagonal (sp4Sign F)).det * (diagonal (sp4Sign F)).det = 1 := by
    rw [← det_mul, diagonal_sp4Sign_mul_self, det_one]
  have h2 : (X.submatrix sp4Index sp4Index).det = X.det :=
    det_submatrix_equiv_self sp4IndexEquiv X
  rw [sp4Mat, det_mul, det_mul, h2, mul_comm _ X.det, mul_assoc, hD, mul_one]

theorem det_mat_statedSp_two (g : StatedSp 2 F) : (mat 2 F g).det = 1 := by
  rw [mat_apply]
  exact SymplecticGroup.det_eq_one (TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup.mp
    ((CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := 2) (K := F)).le g.2))

@[expose] def sp4ToSL4 : StatedSp 2 F →* SL(4, F) where
  toFun g := ⟨sp4Mat (mat 2 F g), by rw [det_sp4Mat, det_mat_statedSp_two]⟩
  map_one' := Subtype.ext (by
    change sp4Mat (mat 2 F 1) = 1
    rw [map_one, sp4Mat_one])
  map_mul' g h := Subtype.ext (by
    change sp4Mat (mat 2 F (g * h)) = sp4Mat (mat 2 F g) * sp4Mat (mat 2 F h)
    rw [map_mul, sp4Mat_mul])

theorem mat_spBlock_one_tv01 (c : F) :
    mat 2 F (spBlock F 1 (tv 0 1 c)) = 1 + c • E F (.positiveLong 1) := by
  rw [spBlock_one_eq_longBlock, tv01_eq_sl2Upper, longBlock_sl2Upper, mat_elt]

theorem mat_spBlock_one_tv10 (c : F) :
    mat 2 F (spBlock F 1 (tv 1 0 c)) = 1 + c • E F (.negativeLong 1) := by
  rw [spBlock_one_eq_longBlock, tv10_eq_sl2Lower, longBlock_sl2Lower, mat_elt]

theorem mat_spBlock_zero_tv01 (c : F) :
    mat 2 F (spBlock F 0 (tv 0 1 c)) =
      1 + c • E F (.difference 0 1 (zero_ne_one : (0 : Fin 2) ≠ 1)) := by
  rw [spBlock_zero_eq_shortBlock, tv01_eq_sl2Upper, shortBlock_sl2Upper, mat_elt]

theorem mat_spBlock_zero_tv10 (c : F) :
    mat 2 F (spBlock F 0 (tv 1 0 c)) =
      1 + c • E F (.difference 1 0 (zero_ne_one : (0 : Fin 2) ≠ 1).symm) := by
  rw [spBlock_zero_eq_shortBlock, tv10_eq_sl2Lower, shortBlock_sl2Lower, mat_elt]

theorem tv_val {n : ℕ} {i j : Fin n} (h : i ≠ j) (c : F) :
    (tv i j c : SL(n, F)).val = 1 + single i j c := by
  rw [tv_of_ne h]
  rfl

theorem sp4ToSL4_long_tv01 (c : F) : sp4ToSL4 (spBlock F 1 (tv 0 1 c)) = tv 1 2 c := by
  apply Subtype.ext
  show sp4Mat (mat 2 F (spBlock F 1 (tv 0 1 c))) = (tv 1 2 c : SL(4, F)).val
  rw [mat_spBlock_one_tv01, tv_val (by decide)]
  ext k l
  rw [sp4Mat_apply]
  fin_cases k <;> fin_cases l <;> simp [sp4Index, sp4Sign, E]

theorem sp4ToSL4_long_tv10 (c : F) : sp4ToSL4 (spBlock F 1 (tv 1 0 c)) = tv 2 1 c := by
  apply Subtype.ext
  show sp4Mat (mat 2 F (spBlock F 1 (tv 1 0 c))) = (tv 2 1 c : SL(4, F)).val
  rw [mat_spBlock_one_tv10, tv_val (by decide)]
  ext k l
  rw [sp4Mat_apply]
  fin_cases k <;> fin_cases l <;> simp [sp4Index, sp4Sign, E]

theorem sp4ToSL4_short_tv01 (c : F) :
    sp4ToSL4 (spBlock F 0 (tv 0 1 c)) = tv 0 1 c * tv 2 3 c := by
  apply Subtype.ext
  show sp4Mat (mat 2 F (spBlock F 0 (tv 0 1 c))) =
    (tv 0 1 c : SL(4, F)).val * (tv 2 3 c : SL(4, F)).val
  rw [mat_spBlock_zero_tv01, tv_val (by decide), tv_val (by decide)]
  ext k l
  rw [sp4Mat_apply]
  fin_cases k <;> fin_cases l <;>
    simp [sp4Index, sp4Sign, E, Matrix.mul_apply, Fin.sum_univ_four]

theorem sp4ToSL4_short_tv10 (c : F) :
    sp4ToSL4 (spBlock F 0 (tv 1 0 c)) = tv 1 0 c * tv 3 2 c := by
  apply Subtype.ext
  show sp4Mat (mat 2 F (spBlock F 0 (tv 1 0 c))) =
    (tv 1 0 c : SL(4, F)).val * (tv 3 2 c : SL(4, F)).val
  rw [mat_spBlock_zero_tv10, tv_val (by decide), tv_val (by decide)]
  ext k l
  rw [sp4Mat_apply]
  fin_cases k <;> fin_cases l <;>
    simp [sp4Index, sp4Sign, E, Matrix.mul_apply, Fin.sum_univ_four]

end CFSG.ComponentClassification.CatLeafProof
