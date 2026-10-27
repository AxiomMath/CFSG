module

public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerSUEigen
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerSUField
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerSUGroup

public section

namespace CFSG.ClassicalInvolution.Q3

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg

section Blocks

variable {E : Type} [Field E] (σ : E ≃+* E)

theorem cT_fromBlocks {n m : Type} [Fintype n] [Fintype m] (A : Matrix n n E) (B : Matrix n m E)
    (C : Matrix m n E) (D : Matrix m m E) :
    cT σ (fromBlocks A B C D) = fromBlocks (cT σ A) (cT σ C) (cT σ B) (cT σ D) := by
  simp only [cT, fromBlocks_map, fromBlocks_transpose]

theorem cT_cT (hσ : ∀ z, σ (σ z) = z) {m n : Type} (A : Matrix m n E) : cT σ (cT σ A) = A := by
  ext i j
  simp [cT, hσ]

end Blocks

section Gram

variable {E : Type} [Field E] (σ : E ≃+* E)

theorem eigen_gram_eq {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    {G g : Matrix ι ι E} (hg : cT σ g * G * g = G) {Q : Matrix ι ι' E} {D : Matrix ι' ι' E}
    (hQ : g * Q = Q * D) : cT σ D * (cT σ Q * G * Q) * D = cT σ Q * G * Q := by
  calc cT σ D * (cT σ Q * G * Q) * D = cT σ (Q * D) * G * (Q * D) := by
        rw [cT_mul]
        simp only [Matrix.mul_assoc]
    _ = cT σ (g * Q) * G * (g * Q) := by rw [hQ]
    _ = cT σ Q * (cT σ g * G * g) * Q := by
        rw [cT_mul]
        simp only [Matrix.mul_assoc]
    _ = cT σ Q * G * Q := by rw [hg]

theorem cT_diag_mul_mul_diag {a b : ℕ} (μ : E) (M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E) :
    cT σ (fromBlocks (μ • (1 : Matrix (Fin a) (Fin a) E)) 0 0
        ((-μ) • (1 : Matrix (Fin b) (Fin b) E))) * M *
      fromBlocks (μ • (1 : Matrix (Fin a) (Fin a) E)) 0 0
        ((-μ) • (1 : Matrix (Fin b) (Fin b) E)) =
    fromBlocks ((σ μ * μ) • M.toBlocks₁₁) ((σ μ * -μ) • M.toBlocks₁₂)
      ((σ (-μ) * μ) • M.toBlocks₂₁) ((σ (-μ) * -μ) • M.toBlocks₂₂) := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  rw [cT_fromBlocks]
  have h0 : cT σ (0 : Matrix (Fin a) (Fin b) E) = 0 := by simp [cT]
  have h0' : cT σ (0 : Matrix (Fin b) (Fin a) E) = 0 := by simp [cT]
  simp only [cT_smul, cT_one, h0, h0', fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    smul_smul]
  simp only [mul_comm μ (σ μ), mul_comm (-μ) (σ μ), mul_comm μ (σ (-μ)),
    mul_comm (-μ) (σ (-μ))]

end Gram

section NormalOne

variable {E : Type} [Field E] [Finite E] [Fact (Nat.Prime 3)] [CharP E 3] {ι : Type} [Fintype ι]
  [DecidableEq ι]

omit [DecidableEq ι] in
theorem cT_gram_eq_self (hE : Nat.card E = 9) {ι' : Type} [Fintype ι'] [DecidableEq ι']
    {H : Matrix ι ι E} (hH : cT (unitaryInvolution E 3 1) H = H) (Q : Matrix ι ι' E) :
    cT (unitaryInvolution E 3 1) (cT (unitaryInvolution E 3 1) Q * H * Q) =
      cT (unitaryInvolution E 3 1) Q * H * Q := by
  rw [cT_mul, cT_mul, hH, cT_cT _ (unitaryInvolution_involutive (card_sq_of_card_nine hE))]
  simp only [Matrix.mul_assoc]

theorem gram_mul_inv_eq_one {ι' : Type} [Fintype ι'] [DecidableEq ι'] {G : Matrix ι ι E}
    (hG : IsUnit G.det) {Q : Matrix ι ι' E} {Q' : Matrix ι' ι E} (h1 : Q * Q' = 1)
    (h2 : Q' * Q = 1) :
    (cT (unitaryInvolution E 3 1) Q * G * Q) *
      (Q' * G⁻¹ * cT (unitaryInvolution E 3 1) Q') = 1 := by
  have hc : cT (unitaryInvolution E 3 1) Q * cT (unitaryInvolution E 3 1) Q' = 1 := by
    rw [← cT_mul, h2, cT_one]
  calc (cT (unitaryInvolution E 3 1) Q * G * Q) *
        (Q' * G⁻¹ * cT (unitaryInvolution E 3 1) Q')
      = cT (unitaryInvolution E 3 1) Q * (G * (Q * Q') * G⁻¹) *
          cT (unitaryInvolution E 3 1) Q' := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.mul_one, Matrix.mul_nonsing_inv _ hG, Matrix.mul_one, hc]

omit [Finite E] [Fact (Nat.Prime 3)] [CharP E 3] in
theorem two_mul_ne_zero_of_pow_four {μ : E} (h2 : (2 : E) ≠ 0) (hμ : μ ^ 4 = 1 ∨ μ ^ 4 = -1) :
    (2 : E) * μ ≠ 0 := by
  refine mul_ne_zero h2 fun h0 => ?_
  rw [h0] at hμ
  rcases hμ with h | h <;> norm_num at h

omit [Finite E] [Fact (Nat.Prime 3)] [CharP E 3] in
theorem eq_zero_of_neg_one_smul_eq {n m : Type} (h2 : (2 : E) ≠ 0) {B : Matrix n m E}
    (h : (-1 : E) • B = B) : B = 0 := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul, neg_mul, one_mul] at this
  have h' : (2 : E) * B i j = 0 := by linear_combination -this
  simpa using (mul_eq_zero.mp h').resolve_left h2

theorem exists_normal_form_one (hE : Nat.card E = 9) {G g : Matrix ι ι E} {μ : E}
    (hμ : μ ^ 4 = 1) (hGh : cT (unitaryInvolution E 3 1) G = G) (hGdet : IsUnit G.det)
    (hg : cT (unitaryInvolution E 3 1) g * G * g = G) (hgg : g * g = (μ * μ) • 1) :
    ∃ (a b : ℕ) (Q : Matrix ι (Fin a ⊕ Fin b) E) (Q' : Matrix (Fin a ⊕ Fin b) ι E),
      Q * Q' = 1 ∧ Q' * Q = 1 ∧ cT (unitaryInvolution E 3 1) Q * G * Q = 1 ∧
        g * Q = Q * fromBlocks (μ • (1 : Matrix (Fin a) (Fin a) E)) 0 0
          ((-μ) • (1 : Matrix (Fin b) (Fin b) E)) := by
  have hE' := card_sq_of_card_nine hE
  have h2 : (2 : E) ≠ 0 := two_ne_zero_of_charP_three
  obtain ⟨a, b, Q₀, Q₀', h1, h2', hgQ⟩ :=
    exists_eigenbasis_matrix (two_mul_ne_zero_of_pow_four h2 (Or.inl hμ))
      (g := g) (μ := μ) hgg
  set D : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E :=
    fromBlocks (μ • (1 : Matrix (Fin a) (Fin a) E)) 0 0
      ((-μ) • (1 : Matrix (Fin b) (Fin b) E)) with hD
  set M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E :=
    cT (unitaryInvolution E 3 1) Q₀ * G * Q₀ with hMdef
  have hM : cT (unitaryInvolution E 3 1) D * M * D = M := eigen_gram_eq _ hg hgQ
  rw [hD, cT_diag_mul_mul_diag] at hM
  conv_rhs at hM => rw [← fromBlocks_toBlocks M]
  obtain ⟨-, hB, hC, -⟩ := fromBlocks_inj.mp hM
  have hs1 : unitaryInvolution E 3 1 μ * -μ = -1 := by
    rw [mul_neg, sigma_mul_self, hμ]
  have hs2 : unitaryInvolution E 3 1 (-μ) * μ = -1 := by
    rw [map_neg, neg_mul, sigma_mul_self, hμ]
  rw [hs1] at hB
  rw [hs2] at hC
  have hB0 := eq_zero_of_neg_one_smul_eq h2 hB
  have hC0 := eq_zero_of_neg_one_smul_eq h2 hC
  have hMeq : M = fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks M]
    rw [hB0, hC0]
  have hherm : cT (unitaryInvolution E 3 1) M = M := cT_gram_eq_self hE hGh Q₀
  have hh : cT (unitaryInvolution E 3 1) M.toBlocks₁₁ = M.toBlocks₁₁ ∧
      cT (unitaryInvolution E 3 1) M.toBlocks₂₂ = M.toBlocks₂₂ := by
    have h' := hherm
    rw [hMeq, cT_fromBlocks] at h'
    have := fromBlocks_inj.mp h'
    exact ⟨this.1, this.2.2.2⟩
  have hdetM : IsUnit M.det := isUnit_det_of_right_inverse (gram_mul_inv_eq_one hGdet h1 h2')
  have hdet : M.toBlocks₁₁.det ≠ 0 ∧ M.toBlocks₂₂.det ≠ 0 := by
    have := hdetM.ne_zero
    rw [hMeq, det_fromBlocks_zero₂₁] at this
    exact ⟨left_ne_zero_of_mul this, right_ne_zero_of_mul this⟩
  obtain ⟨P₁, hP₁⟩ := exists_conjTr_mul_mul_eq_one hE' hh.1 hdet.1
  obtain ⟨P₂, hP₂⟩ := exists_conjTr_mul_mul_eq_one hE' hh.2 hdet.2
  set S : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E :=
    fromBlocks (P₁ : Matrix (Fin a) (Fin a) E) 0 0 (P₂ : Matrix (Fin b) (Fin b) E) with hS
  set S' : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E :=
    fromBlocks ((P₁⁻¹ : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) 0 0
      ((P₂⁻¹ : GL (Fin b) E) : Matrix (Fin b) (Fin b) E) with hS'
  have hSS' : S * S' = 1 := by
    rw [hS, hS', fromBlocks_multiply]
    simp
  have hS'S : S' * S = 1 := by
    rw [hS, hS', fromBlocks_multiply]
    simp
  refine ⟨a, b, Q₀ * S, S' * Q₀', ?_, ?_, ?_, ?_⟩
  · calc Q₀ * S * (S' * Q₀') = Q₀ * (S * S') * Q₀' := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hSS', Matrix.mul_one, h1]
  · calc S' * Q₀' * (Q₀ * S) = S' * (Q₀' * Q₀) * S := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h2', Matrix.mul_one, hS'S]
  · have : cT (unitaryInvolution E 3 1) (Q₀ * S) * G * (Q₀ * S) =
        cT (unitaryInvolution E 3 1) S * M * S := by
      rw [cT_mul, hMdef]
      simp only [Matrix.mul_assoc]
    rw [this, hMeq, hS, cT_fromBlocks]
    have h0 : cT (unitaryInvolution E 3 1) (0 : Matrix (Fin a) (Fin b) E) = 0 := by simp [cT]
    have h0' : cT (unitaryInvolution E 3 1) (0 : Matrix (Fin b) (Fin a) E) = 0 := by simp [cT]
    simp only [h0, h0', fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    have e1 : cT (unitaryInvolution E 3 1) (P₁ : Matrix (Fin a) (Fin a) E) * M.toBlocks₁₁ *
        (P₁ : Matrix (Fin a) (Fin a) E) = 1 := hP₁
    have e2 : cT (unitaryInvolution E 3 1) (P₂ : Matrix (Fin b) (Fin b) E) * M.toBlocks₂₂ *
        (P₂ : Matrix (Fin b) (Fin b) E) = 1 := hP₂
    rw [e1, e2, fromBlocks_one]
  · have hDS : D * S = S * D := by
      rw [hD, hS, fromBlocks_multiply, fromBlocks_multiply]
      simp [Matrix.mul_smul]
    calc g * (Q₀ * S) = (g * Q₀) * S := by rw [Matrix.mul_assoc]
      _ = Q₀ * (D * S) := by rw [hgQ, Matrix.mul_assoc]
      _ = Q₀ * S * D := by rw [hDS, Matrix.mul_assoc]

omit [Finite E] [Fact (Nat.Prime 3)] [CharP E 3] [Fintype ι] [DecidableEq ι] in
theorem le_of_injective_mulVec {a b : ℕ} {C : Matrix (Fin b) (Fin a) E}
    (h : Function.Injective C.mulVec) : a ≤ b := by
  have := LinearMap.finrank_le_finrank_of_injective (f := C.mulVecLin) h
  simpa [Module.finrank_fintype_fun_eq_card] using this

omit [Finite E] [Fact (Nat.Prime 3)] [CharP E 3] [Fintype ι] [DecidableEq ι] in
theorem injective_mulVec_of_isUnit_fromBlocks_zero {a b : ℕ} (B : Matrix (Fin a) (Fin b) E)
    (C : Matrix (Fin b) (Fin a) E)
    (h : IsUnit (fromBlocks 0 B C 0 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E).det) :
    Function.Injective C.mulVec ∧ Function.Injective B.mulVec := by
  have hinj : Function.Injective
      (fromBlocks 0 B C 0 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr h)
  refine ⟨fun x y hxy => ?_, fun x y hxy => ?_⟩
  · have := hinj (a₁ := Sum.elim x 0) (a₂ := Sum.elim y 0) (by
      rw [fromBlocks_mulVec, fromBlocks_mulVec]
      simp [Sum.elim_comp_inl, Sum.elim_comp_inr, hxy])
    simpa using congrArg (fun z => z ∘ Sum.inl) this
  · have := hinj (a₁ := Sum.elim 0 x) (a₂ := Sum.elim 0 y) (by
      rw [fromBlocks_mulVec, fromBlocks_mulVec]
      simp [Sum.elim_comp_inl, Sum.elim_comp_inr, hxy])
    simpa using congrArg (fun z => z ∘ Sum.inr) this

omit [Finite E] [Fact (Nat.Prime 3)] [CharP E 3] [Fintype ι] [DecidableEq ι] in
theorem eq_of_isUnit_fromBlocks_zero {a b : ℕ} (B : Matrix (Fin a) (Fin b) E)
    (C : Matrix (Fin b) (Fin a) E)
    (h : IsUnit (fromBlocks 0 B C 0 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E).det) :
    a = b := by
  obtain ⟨h1, h2⟩ := injective_mulVec_of_isUnit_fromBlocks_zero B C h
  exact le_antisymm (le_of_injective_mulVec h1) (le_of_injective_mulVec h2)

theorem exists_normal_form_hyp (hE : Nat.card E = 9) {G g : Matrix ι ι E} {μ : E}
    (hμ : μ ^ 4 = -1) (hGh : cT (unitaryInvolution E 3 1) G = G) (hGdet : IsUnit G.det)
    (hg : cT (unitaryInvolution E 3 1) g * G * g = G) (hgg : g * g = (μ * μ) • 1) :
    ∃ (m : ℕ) (Q : Matrix ι (Fin m ⊕ Fin m) E) (Q' : Matrix (Fin m ⊕ Fin m) ι E),
      Q * Q' = 1 ∧ Q' * Q = 1 ∧ cT (unitaryInvolution E 3 1) Q * G * Q = fromBlocks 0 1 1 0 ∧
        g * Q = Q * fromBlocks (μ • (1 : Matrix (Fin m) (Fin m) E)) 0 0
          ((-μ) • (1 : Matrix (Fin m) (Fin m) E)) := by
  have h2 : (2 : E) ≠ 0 := two_ne_zero_of_charP_three
  obtain ⟨a, b, Q₀, Q₀', h1, h2', hgQ⟩ :=
    exists_eigenbasis_matrix (two_mul_ne_zero_of_pow_four h2 (Or.inr hμ))
      (g := g) (μ := μ) hgg
  have hM : cT (unitaryInvolution E 3 1)
      (fromBlocks (μ • (1 : Matrix (Fin a) (Fin a) E)) 0 0
        ((-μ) • (1 : Matrix (Fin b) (Fin b) E))) *
      (cT (unitaryInvolution E 3 1) Q₀ * G * Q₀) *
      fromBlocks (μ • (1 : Matrix (Fin a) (Fin a) E)) 0 0
        ((-μ) • (1 : Matrix (Fin b) (Fin b) E)) =
      cT (unitaryInvolution E 3 1) Q₀ * G * Q₀ := eigen_gram_eq _ hg hgQ
  rw [cT_diag_mul_mul_diag] at hM
  conv_rhs at hM => rw [← fromBlocks_toBlocks (cT (unitaryInvolution E 3 1) Q₀ * G * Q₀)]
  obtain ⟨hA, -, -, hD⟩ := fromBlocks_inj.mp hM
  have hs1 : unitaryInvolution E 3 1 μ * μ = -1 := by rw [sigma_mul_self, hμ]
  have hs2 : unitaryInvolution E 3 1 (-μ) * -μ = -1 := by
    rw [map_neg, neg_mul_neg, sigma_mul_self, hμ]
  rw [hs1] at hA
  rw [hs2] at hD
  have hA0 := eq_zero_of_neg_one_smul_eq h2 hA
  have hD0 := eq_zero_of_neg_one_smul_eq h2 hD
  set M := cT (unitaryInvolution E 3 1) Q₀ * G * Q₀ with hMdef
  have hMeq : M = fromBlocks 0 M.toBlocks₁₂ M.toBlocks₂₁ 0 := by
    conv_lhs => rw [← fromBlocks_toBlocks M]
    rw [hA0, hD0]
  have hherm : cT (unitaryInvolution E 3 1) M = M := cT_gram_eq_self hE hGh Q₀
  have hC : M.toBlocks₂₁ = cT (unitaryInvolution E 3 1) M.toBlocks₁₂ := by
    have h' := hherm
    rw [hMeq, cT_fromBlocks] at h'
    exact ((fromBlocks_inj.mp h').2.2.1).symm
  have hdetM : IsUnit M.det := isUnit_det_of_right_inverse (gram_mul_inv_eq_one hGdet h1 h2')
  rw [hMeq] at hdetM
  have hab : a = b := eq_of_isUnit_fromBlocks_zero _ _ hdetM
  subst hab
  obtain ⟨-, hBinj⟩ := injective_mulVec_of_isUnit_fromBlocks_zero _ _ hdetM
  have hBu : IsUnit M.toBlocks₁₂.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hBinj)
  set B := M.toBlocks₁₂ with hB
  have hBB : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hBu
  have hBB' : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hBu
  set D : Matrix (Fin a ⊕ Fin a) (Fin a ⊕ Fin a) E :=
    fromBlocks (μ • (1 : Matrix (Fin a) (Fin a) E)) 0 0 ((-μ) • (1 : Matrix (Fin a) (Fin a) E))
    with hD'
  set S : Matrix (Fin a ⊕ Fin a) (Fin a ⊕ Fin a) E := fromBlocks 1 0 0 B⁻¹ with hS
  set S' : Matrix (Fin a ⊕ Fin a) (Fin a ⊕ Fin a) E := fromBlocks 1 0 0 B with hS'
  have hSS' : S * S' = 1 := by
    rw [hS, hS', fromBlocks_multiply]
    simp [hBB']
  have hS'S : S' * S = 1 := by
    rw [hS, hS', fromBlocks_multiply]
    simp [hBB]
  refine ⟨a, Q₀ * S, S' * Q₀', ?_, ?_, ?_, ?_⟩
  · calc Q₀ * S * (S' * Q₀') = Q₀ * (S * S') * Q₀' := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hSS', Matrix.mul_one, h1]
  · calc S' * Q₀' * (Q₀ * S) = S' * (Q₀' * Q₀) * S := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h2', Matrix.mul_one, hS'S]
  · have : cT (unitaryInvolution E 3 1) (Q₀ * S) * G * (Q₀ * S) =
        cT (unitaryInvolution E 3 1) S * M * S := by
      rw [cT_mul, hMdef]
      simp only [Matrix.mul_assoc]
    rw [this, hMeq, hS, cT_fromBlocks, hC]
    have h0 : cT (unitaryInvolution E 3 1) (0 : Matrix (Fin a) (Fin a) E) = 0 := by simp [cT]
    have hcB : cT (unitaryInvolution E 3 1) B⁻¹ * cT (unitaryInvolution E 3 1) B = 1 := by
      rw [← cT_mul, hBB, cT_one]
    simp only [h0, cT_one, fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero,
      zero_add, Matrix.one_mul, Matrix.mul_one, hBB, hcB]
  · have hDS : D * S = S * D := by
      rw [hD', hS, fromBlocks_multiply, fromBlocks_multiply]
      simp
    calc g * (Q₀ * S) = (g * Q₀) * S := by rw [Matrix.mul_assoc]
      _ = Q₀ * (D * S) := by rw [hgQ, Matrix.mul_assoc]
      _ = Q₀ * S * D := by rw [hDS, Matrix.mul_assoc]

end NormalOne

end CFSG.ClassicalInvolution.Q3
