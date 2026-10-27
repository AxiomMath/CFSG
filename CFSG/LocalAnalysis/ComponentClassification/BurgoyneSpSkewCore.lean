module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSkewNormal

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Sp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.Burgoyne.Proj
open scoped commutatorElement MatrixGroups

variable {r : ℕ} {K : Type} [Field K]

abbrev epsM (d : K) (W₁ W₂ : Matrix (Fin r) (Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  fromBlocks W₁ (d • W₂) W₂ W₁

theorem epsM_mul (d : K) (W₁ W₂ V₁ V₂ : Matrix (Fin r) (Fin r) K) :
    epsM d W₁ W₂ * epsM d V₁ V₂ = epsM d (W₁ * V₁ + d • (W₂ * V₂)) (W₁ * V₂ + W₂ * V₁) := by
  rw [epsM, epsM, epsM, fromBlocks_multiply]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_add]
  congr 1 <;> abel

theorem skewNs_eq_epsM (d : K) : skewNs r K d = epsM d 0 1 := rfl

theorem epsM_commute_skewNs (d : K) (W₁ W₂ : Matrix (Fin r) (Fin r) K) :
    epsM d W₁ W₂ * skewNs r K d = skewNs r K d * epsM d W₁ W₂ := by
  rw [skewNs_eq_epsM, epsM_mul, epsM_mul]
  simp

theorem eq_epsM_of_commute {d : K} {M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (h : M * skewNs r K d = skewNs r K d * M) :
    M = epsM d M.toBlocks₁₁ M.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  rw [← fromBlocks_toBlocks M, skewNs, fromBlocks_multiply, fromBlocks_multiply] at h
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.zero_mul,
    Matrix.one_mul, zero_add, add_zero] at h
  obtain ⟨h11, -, h21, -⟩ := Matrix.fromBlocks_inj.1 h
  rw [epsM, h11, ← h21]

theorem epsM_conds {d : K} {W₁ W₂ : Matrix (Fin r) (Fin r) K} (h1 : W₁ᵀ = -W₁) (h2 : W₂ᵀ = W₂)
    (h3 : W₁ * W₁ + d • (W₂ * W₂) = 0) (h4 : W₁ * W₂ + W₂ * W₁ = 0) :
    (epsM d W₁ W₂)ᵀ * formJ r K + formJ r K * epsM d W₁ W₂ = 0 ∧
      (epsM d W₁ W₂)ᵀ * formJ r K * epsM d W₁ W₂ = 0 ∧ epsM d W₁ W₂ * epsM d W₁ W₂ = 0 := by
  have hsq : epsM d W₁ W₂ * epsM d W₁ W₂ = 0 := by
    rw [epsM_mul, h3, h4, epsM]
    simp [fromBlocks_zero]
  have hJ : (epsM d W₁ W₂)ᵀ * formJ r K + formJ r K * epsM d W₁ W₂ = 0 := by
    rw [epsM, fromBlocks_transpose, formJ, fromBlocks_multiply, fromBlocks_multiply, h1, h2,
      transpose_smul, h2, fromBlocks_add, ← fromBlocks_zero]
    simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, Matrix.zero_mul, Matrix.one_mul,
      Matrix.neg_mul, zero_add, add_zero]
    congr 1 <;> abel
  refine ⟨hJ, ?_, hsq⟩
  have e : (epsM d W₁ W₂)ᵀ * formJ r K = -(formJ r K * epsM d W₁ W₂) :=
    eq_neg_of_add_eq_zero_left hJ
  rw [e, Matrix.neg_mul, Matrix.mul_assoc, hsq, Matrix.mul_zero, neg_zero]

section Transvections

variable {i j : Fin r}

abbrev wSym (i j : Fin r) (a : K) : Matrix (Fin r) (Fin r) K :=
  single i i 1 - single j j 1 + a • (single i j 1 + single j i 1)

abbrev wAnti (i j : Fin r) (b' : K) : Matrix (Fin r) (Fin r) K :=
  b' • (single j i 1 - single i j 1)

theorem wSym_transpose (a : K) : (wSym i j a)ᵀ = wSym i j a := by
  rw [wSym, transpose_add, transpose_sub, transpose_smul, transpose_add, transpose_single,
    transpose_single, transpose_single, transpose_single, add_comm (single j i 1)]

theorem wAnti_transpose (b' : K) : (wAnti i j b')ᵀ = -wAnti i j b' := by
  rw [wAnti, transpose_smul, transpose_sub, transpose_single, transpose_single, ← smul_neg,
    neg_sub]

omit [Field K] in
theorem single_mul_single_ne_zero {R : Type} [Ring R] (hij : i ≠ j) (x y : Fin r) :
    single x i (1 : R) * single j y 1 = 0 ∧ single x j (1 : R) * single i y 1 = 0 :=
  ⟨single_mul_single_of_ne (1 : R) x i j hij 1, single_mul_single_of_ne (1 : R) x j i hij.symm 1⟩

theorem wAnti_sq (hij : i ≠ j) (b' : K) :
    wAnti i j b' * wAnti i j b' = (-(b' * b')) • (single i i 1 + single j j 1) := by
  have e1 := fun x y => (single_mul_single_ne_zero (R := K) hij x y).1
  have e2 := fun x y => (single_mul_single_ne_zero (R := K) hij x y).2
  simp only [wAnti, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
    single_mul_single_same, mul_one, e1, e2]
  module

theorem wSym_sq (hij : i ≠ j) (a : K) :
    wSym i j a * wSym i j a = (1 + a * a) • (single i i 1 + single j j 1) := by
  have e1 := fun x y => (single_mul_single_ne_zero (R := K) hij x y).1
  have e2 := fun x y => (single_mul_single_ne_zero (R := K) hij x y).2
  simp only [wSym, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, single_mul_single_same, mul_one, e1, e2]
  module

theorem wAnti_wSym (hij : i ≠ j) (a b' : K) :
    wAnti i j b' * wSym i j a + wSym i j a * wAnti i j b' = 0 := by
  have e1 := fun x y => (single_mul_single_ne_zero (R := K) hij x y).1
  have e2 := fun x y => (single_mul_single_ne_zero (R := K) hij x y).2
  simp only [wSym, wAnti, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, single_mul_single_same, mul_one, e1, e2]
  module

abbrev skN (d : K) (i j : Fin r) (a b' : K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  epsM d (wAnti i j b') (wSym i j a)

theorem skN_conds (hij : i ≠ j) {d a b : K} (hab : a ^ 2 - d * b ^ 2 = -1) :
    (skN d i j a (b * d))ᵀ * formJ r K + formJ r K * skN d i j a (b * d) = 0 ∧
      (skN d i j a (b * d))ᵀ * formJ r K * skN d i j a (b * d) = 0 ∧
      skN d i j a (b * d) * skN d i j a (b * d) = 0 := by
  refine epsM_conds (wAnti_transpose _) (wSym_transpose _) ?_ (wAnti_wSym hij _ _)
  rw [wAnti_sq hij, wSym_sq hij, smul_smul, ← add_smul]
  have e : -(b * d * (b * d)) + d * (1 + a * a) = 0 := by linear_combination d * hab
  rw [e, zero_smul]

theorem skN_commute (d : K) (i j : Fin r) (a b' : K) :
    skN d i j a b' * skewNs r K d = skewNs r K d * skN d i j a b' :=
  epsM_commute_skewNs d _ _

theorem skN_apply_ne_zero (hij : i ≠ j) (d a b' : K) :
    skN d i j a b' (Sum.inr i) (Sum.inl i) ≠ 0 := by
  simp [Ne.symm hij]

theorem mul_wAnti_apply (hij : i ≠ j) (P : Matrix (Fin r) (Fin r) K) (b' : K) :
    (P * wAnti i j b') j i = b' * P j j := by
  simp [wAnti, Matrix.mul_apply, single_apply, Ne.symm hij, mul_comm]

theorem wAnti_mul_apply (hij : i ≠ j) (P : Matrix (Fin r) (Fin r) K) (b' : K) :
    (wAnti i j b' * P) j i = b' * P i i := by
  simp [wAnti, Matrix.mul_apply, single_apply, hij]

theorem mul_wSym_apply (hij : i ≠ j) (P : Matrix (Fin r) (Fin r) K) (a : K) :
    (P * wSym i j a) j i = P j i + a * P j j := by
  simp [wSym, Matrix.mul_apply, single_apply, Ne.symm hij, Finset.sum_add_distrib, mul_add,
    mul_comm]

theorem wSym_mul_apply (hij : i ≠ j) (P : Matrix (Fin r) (Fin r) K) (a : K) :
    (wSym i j a * P) j i = a * P i i - P j i := by
  simp [wSym, Matrix.mul_apply, single_apply, hij, Finset.sum_add_distrib, sub_eq_add_neg,
    add_mul]
  ring

theorem entries_of_commute_skN (hij : i ≠ j) {d a b' : K} {P R : Matrix (Fin r) (Fin r) K}
    (h : epsM d P R * skN d i j a b' = skN d i j a b' * epsM d P R) :
    b' * P j j + d * (R j i + a * R j j) = b' * P i i + d * (a * R i i - R j i) ∧
      P j i + a * P j j + b' * R j j = b' * R i i + (a * P i i - P j i) := by
  rw [skN, epsM_mul, epsM_mul, epsM, epsM] at h
  obtain ⟨h11, -, h21, -⟩ := Matrix.fromBlocks_inj.1 h
  have e1 := congrFun (congrFun h11 j) i
  have e2 := congrFun (congrFun h21 j) i
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_wAnti_apply hij,
    wAnti_mul_apply hij, mul_wSym_apply hij, wSym_mul_apply hij] at e1 e2
  exact ⟨e1, e2⟩

end Transvections

theorem eq_add_smul_of_commute_skN (hr : 1 ≤ r) (h2 : (2 : K) ≠ 0) {d a b : K} (hd0 : d ≠ 0)
    (hab : a ^ 2 - d * b ^ 2 = -1) {M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hMA : M * skewNs r K d = skewNs r K d * M)
    (hMN : ∀ i j : Fin r, i ≠ j →
      M * skN d i j a (b * d) = skN d i j a (b * d) * M ∧
        M * skN d i j (-a) (-b * d) = skN d i j (-a) (-b * d) * M) :
    ∃ p q : K, M = p • 1 + q • skewNs r K d := by
  set P := M.toBlocks₁₁ with hP
  set R := M.toBlocks₂₁ with hR
  have hM : M = epsM d P R := eq_epsM_of_commute hMA
  have key : ∀ i j : Fin r, i ≠ j → P j i = 0 ∧ R j i = 0 ∧ P j j = P i i ∧ R j j = R i i := by
    intro i j hij
    obtain ⟨h1, h2'⟩ := hMN i j hij
    rw [hM] at h1 h2'
    obtain ⟨e1, e2⟩ := entries_of_commute_skN hij h1
    obtain ⟨f1, f2⟩ := entries_of_commute_skN hij h2'
    have h4 : (2 * 2 : K) ≠ 0 := mul_ne_zero h2 h2
    have hPji : P j i = 0 := by
      have : (2 * 2 : K) * P j i = 0 := by linear_combination e2 + f2
      exact (mul_eq_zero.1 this).resolve_left h4
    have hRji : R j i = 0 := by
      have : (2 * 2 * d) * R j i = 0 := by linear_combination e1 + f1
      exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero h4 hd0)
    have g1 : a * (P j j - P i i) + b * d * (R j j - R i i) = 0 := by
      have : 2 * (a * (P j j - P i i) + b * d * (R j j - R i i)) = 0 := by
        linear_combination e2 - f2
      exact (mul_eq_zero.1 this).resolve_left h2
    have g2 : b * (P j j - P i i) + a * (R j j - R i i) = 0 := by
      have : (2 * d) * (b * (P j j - P i i) + a * (R j j - R i i)) = 0 := by
        linear_combination e1 - f1
      exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero h2 hd0)
    refine ⟨hPji, hRji, ?_, ?_⟩
    · linear_combination (-a) * g1 + b * d * g2 + (P j j - P i i) * hab
    · linear_combination b * g1 - a * g2 + (R j j - R i i) * hab
  set i₀ : Fin r := ⟨0, by omega⟩
  have hdiag : ∀ (X : Matrix (Fin r) (Fin r) K),
      (∀ i j : Fin r, i ≠ j → X j i = 0 ∧ X j j = X i i) → X = X i₀ i₀ • 1 := by
    intro X hX
    ext k l
    rw [Matrix.smul_apply, one_apply, smul_eq_mul]
    by_cases hkl : k = l
    · subst hkl
      simp only [↓reduceIte, mul_one]
      by_cases hk : k = i₀
      · rw [hk]
      · exact (hX i₀ k (Ne.symm hk)).2
    · simp only [hkl, ↓reduceIte, mul_zero]
      exact (hX l k (Ne.symm hkl)).1
  have hPs := hdiag P fun i j hij => ⟨(key i j hij).1, (key i j hij).2.2.1⟩
  have hRs := hdiag R fun i j hij => ⟨(key i j hij).2.1, (key i j hij).2.2.2⟩
  refine ⟨P i₀ i₀, R i₀ i₀, ?_⟩
  rw [hM, skewNs_eq_epsM]
  conv_lhs => rw [hPs, hRs]
  rw [epsM, epsM, ← fromBlocks_one, fromBlocks_smul, fromBlocks_smul, fromBlocks_add]
  simp [smul_smul, mul_comm]

end CFSG.ComponentClassification.Burgoyne.Sp
