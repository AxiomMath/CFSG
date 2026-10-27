module

public import CFSG.GH74.Generic.S1.LinKron
public import CFSG.LocalAnalysis.ComponentInitial.LinearOrthogonalBasis
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Matrix Module
  CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

variable {F : Type} [Field F]

noncomputable def basisMat (e : Basis (Fin 4) F (Fin 4 → F)) : Matrix (Fin 4) (Fin 4) F :=
  Matrix.of fun r j => e j r

theorem isUnit_det_basisMat (e : Basis (Fin 4) F (Fin 4 → F)) : IsUnit (basisMat e).det := by
  have h : basisMat e = (Pi.basisFun F (Fin 4)).toMatrix e := by
    ext r j
    simp [basisMat, Basis.toMatrix_apply]
  rw [h]
  exact isUnit_det_of_left_inverse (Basis.toMatrix_mul_toMatrix_flip e (Pi.basisFun F (Fin 4)))

theorem gram_basisMat (e : Basis (Fin 4) F (Fin 4 → F)) (S : Matrix (Fin 4) (Fin 4) F) (i j : Fin 4) :
    ((basisMat e)ᵀ * S * basisMat e) i j = Matrix.toBilin' S (e i) (e j) := by
  rw [Matrix.toBilin'_apply', Matrix.mul_assoc]
  rfl

theorem exists_mul_transpose_of_symm [Finite F] (hodd : Odd (Nat.card F))
    (S : Matrix (Fin 4) (Fin 4) F) (hS : Sᵀ = S) (hdet : S.det ≠ 0) (hsq : IsSquare S.det) :
    ∃ P : Matrix (Fin 4) (Fin 4) F, IsUnit P.det ∧ S = P * Pᵀ := by
  classical
  have hBs : (Matrix.toBilin' S).IsSymm := LinearMap.BilinForm.isSymm_def.2 fun x y => by
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', dotProduct_mulVec, ← Matrix.mulVec_transpose,
      hS, dotProduct_comm]
  have hnd : (Matrix.toBilin' S).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.2 hdet
  obtain ⟨h1, h2⟩ := finite_odd_symmetric_equal_value_orthogonal_basis hodd
    (finrank_fin_fun F) (by norm_num) hnd hBs
  obtain ⟨v, hv⟩ := h1 1 one_ne_zero
  obtain ⟨e, he_orth, -, he_val, he_last⟩ := h2 1 v one_ne_zero hv
  set Pe := basisMat e with hPe
  set δ : F := Matrix.toBilin' S (e 3) (e 3) with hδ
  have hδ0 : δ ≠ 0 := he_last 3 (by simp)
  have hgram : Peᵀ * S * Pe = Matrix.diagonal ![1, 1, 1, δ] := by
    ext i j
    rw [hPe, gram_basisMat]
    by_cases hij : i = j
    · subst hij
      fin_cases i
      · simpa using he_val 0 (by simp)
      · simpa using he_val 1 (by simp)
      · simpa using he_val 2 (by simp)
      · simp [hδ]
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact LinearMap.isOrthoᵢ_def.1 he_orth i j hij
  have hdetδ : δ = Pe.det * S.det * Pe.det := by
    have := congrArg Matrix.det hgram
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at this
    simp [Fin.prod_univ_four] at this
    exact this.symm
  obtain ⟨r, hr⟩ := hsq
  set s : F := Pe.det * r with hs
  have hss : s * s = δ := by rw [hdetδ, hr, hs]; ring
  have hs0 : s ≠ 0 := by
    intro h
    apply hδ0
    rw [← hss, h, zero_mul]
  have hPePi : Pe * Pe⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_det_basisMat e)
  set Q : Matrix (Fin 4) (Fin 4) F := Matrix.diagonal ![1, 1, 1, s] with hQ
  refine ⟨(Pe⁻¹)ᵀ * Q, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_transpose, hQ, Matrix.det_diagonal]
    refine IsUnit.mul (isUnit_det_of_left_inverse hPePi) ?_
    simp [Fin.prod_univ_four, hs0]
  · have hQQ : Q * Q = Matrix.diagonal ![1, 1, 1, δ] := by
      rw [hQ, Matrix.diagonal_mul_diagonal]
      congr 1
      ext i
      fin_cases i <;> simp [hss]
    have hQt : Qᵀ = Q := Matrix.diagonal_transpose _
    calc S = (Pe * Pe⁻¹)ᵀ * S * (Pe * Pe⁻¹) := by
          rw [hPePi, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
      _ = (Pe⁻¹)ᵀ * (Peᵀ * S * Pe) * Pe⁻¹ := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (Pe⁻¹)ᵀ * (Q * Q) * Pe⁻¹ := by rw [hgram, hQQ]
      _ = (Pe⁻¹)ᵀ * Q * ((Pe⁻¹)ᵀ * Q)ᵀ := by
          rw [Matrix.transpose_mul, Matrix.transpose_transpose, hQt]
          simp only [Matrix.mul_assoc]

def idx4 : Fin 2 ⊕ Fin 2 ≃ Fin 4 where
  toFun := Sum.elim ![0, 1] ![2, 3]
  invFun := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1]
  left_inv := by rintro (i | i) <;> fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem J_idx4_symm (i j : Fin 4) :
    Matrix.J (Fin 2) F (idx4.symm i) (idx4.symm j) = -skewK i j := by
  fin_cases i <;> fin_cases j <;> simp [skewK, Matrix.J, idx4]

theorem exists_mul_skewK_transpose (h2 : (2 : F) ≠ 0) (g : Matrix (Fin 4) (Fin 4) F)
    (hg : gᵀ = -g) (hdet : g.det ≠ 0) :
    ∃ P : Matrix (Fin 4) (Fin 4) F, IsUnit P.det ∧ g = P * (-skewK) * Pᵀ := by
  classical
  have hBalt : (Matrix.toBilin' g).IsAlt := fun v => by
    rw [Matrix.toBilin'_apply']
    have hx : v ⬝ᵥ (g *ᵥ v) = -(v ⬝ᵥ (g *ᵥ v)) := by
      conv_lhs => rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hg, Matrix.neg_mulVec,
        neg_dotProduct, dotProduct_comm]
    have h3 : (2 : F) * (v ⬝ᵥ (g *ᵥ v)) = 0 := by linear_combination hx
    exact (mul_eq_zero.1 h3).resolve_left h2
  have hBnd : (Matrix.toBilin' g).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.2 hdet
  obtain ⟨m, b, hb⟩ := hBalt.exists_basis_toMatrix_eq_J hBnd
  have hm : m = 2 := by
    have h := Module.finrank_eq_card_basis b
    rw [finrank_fin_fun, Fintype.card_sum, Fintype.card_fin] at h
    omega
  subst hm
  let b4 : Basis (Fin 4) F (Fin 4 → F) := b.reindex idx4
  set Pe := basisMat b4 with hPe
  have hgram : Peᵀ * g * Pe = -skewK := by
    ext i j
    rw [hPe, gram_basisMat]
    have h1 : Matrix.toBilin' g (b4 i) (b4 j) = Matrix.J (Fin 2) F (idx4.symm i) (idx4.symm j) := by
      simp only [b4, Basis.reindex_apply]
      rw [← hb, LinearMap.BilinForm.toMatrix_apply]
    rw [h1, J_idx4_symm]
    rfl
  have hPePi : Pe * Pe⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_det_basisMat b4)
  refine ⟨(Pe⁻¹)ᵀ, ?_, ?_⟩
  · rw [Matrix.det_transpose]
    exact isUnit_det_of_left_inverse hPePi
  · calc g = (Pe * Pe⁻¹)ᵀ * g * (Pe * Pe⁻¹) := by
          rw [hPePi, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
      _ = (Pe⁻¹)ᵀ * (Peᵀ * g * Pe) * Pe⁻¹ := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (Pe⁻¹)ᵀ * (-skewK) * ((Pe⁻¹)ᵀ)ᵀ := by
          rw [hgram, Matrix.transpose_transpose]


theorem exists_mul_hypK_transpose [Finite F] (hodd : Odd (Nat.card F))
    (S : Matrix (Fin 4) (Fin 4) F) (hS : Sᵀ = S) (hdet : S.det ≠ 0) (hsq : IsSquare S.det) :
    ∃ Q : Matrix (Fin 4) (Fin 4) F, IsUnit Q.det ∧ S = Q * hypK * Qᵀ := by
  obtain ⟨P₁, hP₁, h1⟩ := exists_mul_transpose_of_symm hodd S hS hdet hsq
  obtain ⟨P₂, hP₂, h2⟩ := exists_mul_transpose_of_symm hodd (hypK : Matrix (Fin 4) (Fin 4) F)
    hypK_transpose (by rw [det_hypK]; exact one_ne_zero) ⟨1, by rw [det_hypK, mul_one]⟩
  refine ⟨P₁ * P₂⁻¹, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact hP₁.mul (Matrix.isUnit_nonsing_inv_det P₂ hP₂)
  · have hP₂i : P₂⁻¹ * P₂ = 1 := Matrix.nonsing_inv_mul _ hP₂
    calc S = P₁ * P₁ᵀ := h1
      _ = (P₁ * P₂⁻¹) * (P₂ * P₂ᵀ) * (P₁ * P₂⁻¹)ᵀ := by
          have hP₂i' : P₂ᵀ * (P₂⁻¹)ᵀ = 1 := by
            rw [← Matrix.transpose_mul, hP₂i, Matrix.transpose_one]
          rw [Matrix.transpose_mul]
          calc P₁ * P₁ᵀ = P₁ * (P₂⁻¹ * P₂) * (P₂ᵀ * (P₂⁻¹)ᵀ) * P₁ᵀ := by
                rw [hP₂i, hP₂i', Matrix.mul_one, Matrix.mul_one]
            _ = _ := by simp only [Matrix.mul_assoc]
      _ = (P₁ * P₂⁻¹) * hypK * (P₁ * P₂⁻¹)ᵀ := by rw [← h2]

theorem graph_fix (P g : GL (Fin 4) F) (Gf : Matrix (Fin 4) (Fin 4) F)
    (hg : (g : Matrix (Fin 4) (Fin 4) F) =
      (P : Matrix (Fin 4) (Fin 4) F) * Gf * (P : Matrix (Fin 4) (Fin 4) F)ᵀ)
    (X : SL(2, F))
    (hX : kron1 (X : Matrix (Fin 2) (Fin 2) F) * Gf * (kron1 (X : Matrix (Fin 2) (Fin 2) F))ᵀ = Gf) :
    g * GeneralLinearGroup.inverseTranspose (P * kronGL X * P⁻¹) * g⁻¹ = P * kronGL X * P⁻¹ := by
  set k : GL (Fin 4) F := P * kronGL X * P⁻¹ with hk
  set D : Matrix (Fin 4) (Fin 4) F := kron1 (X : Matrix (Fin 2) (Fin 2) F) with hD
  set Pm : Matrix (Fin 4) (Fin 4) F := (P : Matrix (Fin 4) (Fin 4) F) with hPm
  set Pim : Matrix (Fin 4) (Fin 4) F := ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hPim
  have h1 : Pim * Pm = 1 := by rw [hPm, hPim, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : Pmᵀ * Pimᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  have hKm : (k : Matrix (Fin 4) (Fin 4) F) = Pm * D * Pim := by
    rw [hk, Units.val_mul, Units.val_mul]
    rfl
  have hkg : (k : Matrix (Fin 4) (Fin 4) F) * g * (k : Matrix (Fin 4) (Fin 4) F)ᵀ = g := by
    calc (k : Matrix (Fin 4) (Fin 4) F) * g * (k : Matrix (Fin 4) (Fin 4) F)ᵀ
        = Pm * D * (Pim * Pm) * Gf * (Pmᵀ * Pimᵀ) * Dᵀ * Pmᵀ := by
          rw [hKm, hg, Matrix.transpose_mul, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = Pm * (D * Gf * Dᵀ) * Pmᵀ := by
          rw [h1, h2]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = g := by rw [hX, hg]
  have hKiK : ((k⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (k : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_inverseTranspose]
  calc (g : Matrix (Fin 4) (Fin 4) F) * ((k⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ
      = ((k : Matrix (Fin 4) (Fin 4) F) * g * (k : Matrix (Fin 4) (Fin 4) F)ᵀ) *
          ((k⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ := by rw [hkg]
    _ = (k : Matrix (Fin 4) (Fin 4) F) * g *
          (((k⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (k : Matrix (Fin 4) (Fin 4) F))ᵀ := by
        rw [Matrix.transpose_mul, Matrix.mul_assoc _ _ (Matrix.transpose _)]
    _ = (k : Matrix (Fin 4) (Fin 4) F) * g := by rw [hKiK, Matrix.transpose_one, Matrix.mul_one]

theorem graphLike_lin {F : Type} [Field F] [Finite F] (hF : Nat.card F % 4 = 3)
    (α : MulAut ↥(StatedSL 4 F)) (_hα : α * α = 1) (h : IsGraphLike (StatedSL 4 F) α) :
    GoodFixedCentral (Nat.card F = 3) α ∨ IsExoticLin (StatedSL 4 F) α := by
  obtain ⟨g, hgt, hact⟩ := h
  have hodd : Odd (Nat.card F) := Nat.odd_iff.2 (by omega)
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hdetg : (g : Matrix (Fin 4) (Fin 4) F).det ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
  rcases hgt with hsym | hskew
  · by_cases hsq : IsSquare (g : Matrix (Fin 4) (Fin 4) F).det
    · left
      obtain ⟨Q, hQ, hgQ⟩ := exists_mul_hypK_transpose hodd _ hsym hdetg hsq
      let Qg : GL (Fin 4) F := GeneralLinearGroup.mkOfDetNeZero Q hQ.ne_zero
      refine goodFixedCentral_of_phiP hF α Qg fun X => ?_
      rw [hact (phiP Qg X), coe_phiP]
      exact graph_fix Qg g hypK hgQ X (kron1_hypK _ X.2)
    · right
      exact ⟨g, hsym, hsq, hact⟩
  · left
    obtain ⟨P, hP, hgP⟩ := exists_mul_skewK_transpose h2 _ hskew hdetg
    let Pg : GL (Fin 4) F := GeneralLinearGroup.mkOfDetNeZero P hP.ne_zero
    refine goodFixedCentral_of_phiP hF α Pg fun X => ?_
    rw [hact (phiP Pg X), coe_phiP]
    refine graph_fix Pg g (-skewK) hgP X ?_
    rw [Matrix.mul_neg, Matrix.neg_mul, kron1_skewK _ X.2]

end CFSG.GH74.Generic.S1
