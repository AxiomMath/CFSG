module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4NoPSpSym
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4NoPSpBound
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4StabAut
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphTools

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace StabL

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag Blocks

variable {F : Type} [Field F] [Fintype F]

omit [Fintype F] in
theorem polarBilin_toQuadraticForm' {R : Matrix (Fin 4) (Fin 4) F} (hR : Rᵀ = R) :
    QuadraticMap.polarBilin (Matrix.toQuadraticForm' R) = Matrix.toBilin' ((2 : F) • R) := by
  rw [Matrix.toQuadraticForm', LinearMap.BilinMap.polarBilin_toQuadraticMap]
  refine LinearMap.BilinForm.ext fun x y => ?_
  rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.flip_apply, Matrix.toLinearMap₂'_apply',
    Matrix.toLinearMap₂'_apply', Matrix.toBilin'_apply', Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, dotProduct_comm y, ← Matrix.vecMul_transpose R x, ← Matrix.dotProduct_mulVec, hR]
  ring

theorem card_orthogonalGroup_le (hF : Fintype.card F % 4 = 3) {R : Matrix (Fin 4) (Fin 4) F}
    (hR : Rᵀ = R) (hRu : IsUnit R.det) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Matrix.toQuadraticForm' R)) ≤
      2 * Nat.card F ^ 2 * (Nat.card F ^ 4 - 1) := by
  have h2 := two_ne_zero_of_card_mod_four hF
  set Q := Matrix.toQuadraticForm' R with hQ
  have hnd : (QuadraticMap.polarBilin Q).Nondegenerate := by
    rw [hQ, polarBilin_toQuadraticForm' hR]
    apply LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.2
    rw [Matrix.det_smul, Fintype.card_fin]
    exact mul_ne_zero (pow_ne_zero _ h2) hRu.ne_zero
  have hdim : Module.finrank F (Fin 4 → F) = 2 * (1 + 1) := by
    rw [Module.finrank_fin_fun]
  set q := Nat.card F with hq
  have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
  have hbound : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) ≤
      2 * (q : ℤ) ^ 2 * ((q : ℤ) ^ 2 + 1) * ((q : ℤ) ^ 2 - 1) := by
    have hq0 : (1 : ℤ) ≤ (q : ℤ) ^ 2 := by exact_mod_cast hq1
    by_cases hp : CFSG.GroupTheory.WeirSylow.IsPlusType Q
    · rw [CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hnd hdim
        (Or.inl ⟨rfl, hp⟩)]
      simp only [Finset.Icc_self, Finset.prod_singleton, ← hq]
      norm_num
      nlinarith [mul_nonneg (by positivity : (0 : ℤ) ≤ (q : ℤ) ^ 2)
        (by linarith : (0 : ℤ) ≤ (q : ℤ) ^ 2 - 1)]
    · rw [CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hnd hdim
        (Or.inr ⟨rfl, hp⟩)]
      simp only [Finset.Icc_self, Finset.prod_singleton, ← hq, sub_neg_eq_add]
      norm_num
  have hq4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ Nat.card_pos
  have : ((2 * q ^ 2 * (q ^ 4 - 1) : ℕ) : ℤ) = 2 * (q : ℤ) ^ 2 * ((q : ℤ) ^ 2 + 1) *
      ((q : ℤ) ^ 2 - 1) := by
    push_cast [hq4]
    ring
  exact_mod_cast hbound.trans this.symm.le

theorem false_of_fixed_symmetric (hF : Fintype.card F % 4 = 3) (A : GL (Fin 4) F)
    (hA : (A : Matrix (Fin 4) (Fin 4) F)ᵀ = A) {M : Subgroup (projectiveSL 4 F)}
    (hM : ∀ x ∈ M, (conjAut 4 F A * dualAut 4 F) x = x)
    (hcard : 2 * Nat.card M =
      Nat.card F ^ 4 * (Nat.card F ^ 2 - 1) * (Nat.card F ^ 4 - 1)) : False := by
  set R := ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hRdef
  have hRt : Rᵀ = R := by
    rw [hRdef, Matrix.coe_units_inv, Matrix.transpose_nonsing_inv, hA]
  have hRu : IsUnit R.det := by
    rw [hRdef, ← GeneralLinearGroup.val_det_apply]
    exact Units.isUnit _
  have h1 := card_le_of_fixed_conjAut_dualAut hF A hM
  have h2 := card_orthogonalGroup_le hF hRt hRu
  set q := Nat.card F with hq
  have hq3 : 3 ≤ q := by
    rw [hq, Nat.card_eq_fintype_card]
    omega
  set b := q ^ 4 - 1 with hb
  have hb0 : 0 < b := by
    have : 3 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hq3 4
    omega
  have h3 : q ^ 4 * (q ^ 2 - 1) * b ≤ 8 * q ^ 2 * b := by
    rw [← hcard]
    calc 2 * Nat.card M ≤ 2 * (2 * (2 * q ^ 2 * b)) := by
          have := h1.trans (Nat.mul_le_mul_left 2 h2)
          omega
      _ = 8 * q ^ 2 * b := by ring
  have h4 : q ^ 4 * (q ^ 2 - 1) ≤ 8 * q ^ 2 := Nat.le_of_mul_le_mul_right (by
    calc q ^ 4 * (q ^ 2 - 1) * b ≤ 8 * q ^ 2 * b := h3) hb0
  have h5 : q ^ 2 * (q ^ 2 * (q ^ 2 - 1)) ≤ q ^ 2 * 8 := by
    calc q ^ 2 * (q ^ 2 * (q ^ 2 - 1)) = q ^ 4 * (q ^ 2 - 1) := by ring
      _ ≤ 8 * q ^ 2 := h4
      _ = q ^ 2 * 8 := by ring
  have h6 : q ^ 2 * (q ^ 2 - 1) ≤ 8 := Nat.le_of_mul_le_mul_left h5 (by positivity)
  have h7 : 3 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq3 2
  have h8 : 9 * 8 ≤ q ^ 2 * (q ^ 2 - 1) := Nat.mul_le_mul h7 (by omega)
  omega

theorem alternating_of_fixed_psp (hF : Fintype.card F % 4 = 3) {p f : ℕ} (hp : p.Prime)
    (hK : Nat.card F = p ^ f) {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2)
    (hsq : s ∣ Fintype.card F ^ 2 + 1) (α : MulAut (projectiveSL 4 F)) (hα2 : α ^ 2 = 1)
    (hα1 : α ≠ 1) {M : Subgroup (projectiveSL 4 F)} (hM : ∀ x ∈ M, α x = x)
    (hcard : 2 * Nat.card M =
      Nat.card F ^ 4 * (Nat.card F ^ 2 - 1) * (Nat.card F ^ 4 - 1))
    {y : projectiveSL 4 F} (hyM : y ∈ M) (hy : orderOf y = s) :
    ∃ A : GL (Fin 4) F, (A : Matrix (Fin 4) (Fin 4) F)ᵀ = -A ∧
      α = conjAut 4 F A * dualAut 4 F := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := F) (n := 4) (by norm_num)
  obtain ⟨A, σ, ε, hε, rfl⟩ := hgen α
  have hσ := fieldAut_eq_one_of_pow hp hK (odd_of_card_mod_four hF hK) A σ hε (m := 0)
    (by simpa using hα2)
  subst hσ
  simp only [map_one, mul_one] at hM hα1 hα2 ⊢
  interval_cases ε
  · exfalso
    simp only [pow_zero, mul_one] at hM hα1 hα2
    obtain ⟨ν, hν, hns⟩ := sq_eq_nonsquare_of_fixed hF hs hs2 hsq A hα1 hα2 hy (hM y hyM)
    exact false_of_fixed_conjAut hF A ν hν hns hM hcard
  · simp only [pow_one] at hM hα1 hα2 ⊢
    rcases transpose_eq_or_eq_neg_of_sq_conjAut_dualAut (by norm_num) A hα2 with hsym | halt
    · exact (false_of_fixed_symmetric hF A hsym hM hcard).elim
    · exact ⟨A, halt, rfl⟩

end StabL

end CFSG.ComponentClassification.CatFactsL4U4
