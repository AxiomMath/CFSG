module

public import CFSG.GH74.Generic.S1.FrameNorm
public import CFSG.RankThree.PartOne.KC.CommonEigenbasis

public section

namespace CFSG.GH74.Generic.S1

open Matrix Module CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F]

theorem trace_refl (h2 : (2 : F) ≠ 0) {ρ : GL (Fin 4) F} (hρ : ρ * ρ = 1)
    (hdet : (ρ : Matrix (Fin 4) (Fin 4) F).det = -1) :
    Matrix.trace (ρ : Matrix (Fin 4) (Fin 4) F) = 2 ∨
      Matrix.trace (ρ : Matrix (Fin 4) (Fin 4) F) = -2 := by
  obtain ⟨ρ', P, hρ', hP, -⟩ := exists_refl_conj (ringChar_ne_two_of_two_ne_zero h2) hρ hdet
  have h1 : Matrix.trace (ρ' : Matrix (Fin 4) (Fin 4) F) = 2 := by
    have h3 : Matrix.trace ((P⁻¹ * ρ' * P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        Matrix.trace (ρ' : Matrix (Fin 4) (Fin 4) F) := by
      have := Matrix.trace_units_conj P⁻¹ (ρ' : Matrix (Fin 4) (Fin 4) F)
      simpa using this
    rw [← h3, hP]
    change Matrix.trace (reflDiagMat F 3) = 2
    simp [reflDiagMat, Matrix.trace_diagonal, Fin.sum_univ_four]
    norm_num
  rcases hρ' with rfl | rfl
  · exact Or.inl h1
  · right
    rw [Units.val_neg, Matrix.trace_neg] at h1
    linear_combination -h1

theorem mul_comm_of_smul (h2 : (2 : F) ≠ 0) {A B : GL (Fin 4) F} (hA : A * A = 1) (hB : B * B = 1)
    (hdet : (A : Matrix (Fin 4) (Fin 4) F).det = -1) {c : F}
    (h : (A : Matrix (Fin 4) (Fin 4) F) * B = c • ((B : Matrix (Fin 4) (Fin 4) F) * A)) :
    (A : Matrix (Fin 4) (Fin 4) F) * B = (B : Matrix (Fin 4) (Fin 4) F) * A := by
  set Am : Matrix (Fin 4) (Fin 4) F := (A : Matrix (Fin 4) (Fin 4) F) with hAmdef
  set Bm : Matrix (Fin 4) (Fin 4) F := (B : Matrix (Fin 4) (Fin 4) F) with hBmdef
  have hAm : Am * Am = 1 := by rw [hAmdef, ← Units.val_mul, hA, Units.val_one]
  have hBm : Bm * Bm = 1 := by rw [hBmdef, ← Units.val_mul, hB, Units.val_one]
  have hB0 : Bm ≠ 0 := by
    intro h0
    rw [h0, Matrix.zero_mul] at hBm
    exact zero_ne_one hBm
  have h1 : Bm = (c * c) • Bm := by
    calc Bm = Am * (Am * Bm) := by rw [← Matrix.mul_assoc, hAm, Matrix.one_mul]
      _ = Am * (c • (Bm * Am)) := by rw [h]
      _ = c • (Am * Bm * Am) := by rw [Matrix.mul_smul, Matrix.mul_assoc]
      _ = c • (c • (Bm * Am) * Am) := by rw [h]
      _ = (c * c) • Bm := by rw [Matrix.smul_mul, Matrix.mul_assoc, hAm, Matrix.mul_one, smul_smul]
  have hcc : c * c = 1 := by
    have h3 : (c * c - 1) • Bm = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right hB0)
  rcases mul_self_eq_one_iff.1 hcc with hc1 | hc1
  · rw [h, hc1, one_smul]
  · exfalso
    rw [hc1, neg_one_smul] at h
    have htr : Matrix.trace Am = -Matrix.trace Am := by
      calc Matrix.trace Am = Matrix.trace (Am * (Bm * Bm)) := by rw [hBm, Matrix.mul_one]
        _ = Matrix.trace ((Am * Bm) * Bm) := by rw [Matrix.mul_assoc]
        _ = Matrix.trace (-(Bm * Am) * Bm) := by rw [h]
        _ = -Matrix.trace (Bm * (Am * Bm)) := by
            rw [Matrix.neg_mul, Matrix.trace_neg, Matrix.mul_assoc]
        _ = -Matrix.trace ((Am * Bm) * Bm) := by rw [Matrix.trace_mul_comm Bm (Am * Bm)]
        _ = -Matrix.trace (Am * (Bm * Bm)) := by rw [Matrix.mul_assoc]
        _ = -Matrix.trace Am := by rw [hBm, Matrix.mul_one]
    have h22 : (2 : F) * 2 = 0 := by
      rcases trace_refl h2 hA hdet with ht | ht
      · rw [← hAmdef] at ht
        rw [ht] at htr
        linear_combination htr
      · rw [← hAmdef] at ht
        rw [ht] at htr
        linear_combination -htr
    exact h2 (mul_self_eq_zero.1 h22)

@[expose] noncomputable def basisCols (b : Basis (Fin 4) F (Fin 4 → F)) : Matrix (Fin 4) (Fin 4) F :=
  Matrix.of fun r j => b j r

theorem isUnit_det_basisCols (b : Basis (Fin 4) F (Fin 4 → F)) : IsUnit (basisCols b).det := by
  have h : basisCols b = (Pi.basisFun F (Fin 4)).toMatrix b := by
    ext r j
    simp [basisCols, Basis.toMatrix_apply]
  rw [h]
  exact isUnit_det_of_left_inverse (Basis.toMatrix_mul_toMatrix_flip b (Pi.basisFun F (Fin 4)))

@[expose] noncomputable def basisGL (b : Basis (Fin 4) F (Fin 4 → F)) : GL (Fin 4) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (basisCols b) (isUnit_det_basisCols b).ne_zero

theorem coe_basisGL (b : Basis (Fin 4) F (Fin 4 → F)) :
    ((basisGL b : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = basisCols b := rfl

theorem basisGL_conj (b : Basis (Fin 4) F (Fin 4 → F)) (A : GL (Fin 4) F) (μ : Fin 4 → F)
    (hb : ∀ i, (A : Matrix (Fin 4) (Fin 4) F) *ᵥ b i = μ i • b i) :
    ((basisGL b)⁻¹ * A * basisGL b : GL (Fin 4) F) = (diagonal μ : Matrix (Fin 4) (Fin 4) F) := by
  have hAP : (A : Matrix (Fin 4) (Fin 4) F) * basisCols b = basisCols b * diagonal μ := by
    ext a j
    have h := congrFun (hb j) a
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_diagonal]
    simp only [basisCols, Matrix.mul_apply, Matrix.of_apply]
    rw [h, mul_comm]
  have hPiP : ((basisGL b)⁻¹ : GL (Fin 4) F).val * (basisGL b : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc, coe_basisGL, hAP, ← Matrix.mul_assoc]
  rw [coe_basisGL] at hPiP
  rw [hPiP, Matrix.one_mul]

theorem exists_common_eigenbasis_lin (h2 : (2 : F) ≠ 0) (ρ : Fin 4 → GL (Fin 4) F)
    (hρ2 : ∀ j, ρ j * ρ j = 1)
    (hcomm : ∀ j k, (ρ j : Matrix (Fin 4) (Fin 4) F) * ρ k = (ρ k : Matrix (Fin 4) (Fin 4) F) * ρ j) :
    ∃ (b : Basis (Fin 4) F (Fin 4 → F)) (μ : Fin 4 → Fin 4 → F),
      ∀ j i, (ρ j : Matrix (Fin 4) (Fin 4) F) *ᵥ b i = μ j i • b i := by
  have hζ : IsPrimitiveRoot (-1 : F) 2 := by
    have := IsPrimitiveRoot.orderOf (-1 : F)
    simpa [orderOf_neg_one, ringChar_ne_two_of_two_ne_zero h2] using this
  let f : Fin 4 → Module.End F (Fin 4 → F) := fun j =>
    Matrix.toLinAlgEquiv' (ρ j : Matrix (Fin 4) (Fin 4) F)
  have hf_comm : ∀ i j, Commute (f i) (f j) := fun i j => by
    show f i * f j = f j * f i
    simp only [f, ← map_mul, hcomm i j]
  have hf_pow : ∀ j, f j ^ 2 = 1 := fun j => by
    have hm : (ρ j : Matrix (Fin 4) (Fin 4) F) * ρ j = 1 := by
      rw [← Units.val_mul, hρ2 j, Units.val_one]
    simp only [f, sq, ← map_mul, hm, map_one]
  obtain ⟨b, μ, hb⟩ := CFSG.RankThree.PartOne.exists_basis_common_eigenvectors_of_pow_eq_one
    (p := 2) hζ f hf_comm hf_pow
  refine ⟨b.reindex (finCongr (Module.finrank_fin_fun F)),
    fun j i => μ j ((finCongr (Module.finrank_fin_fun F)).symm i), fun j i => ?_⟩
  have := hb j ((finCongr (Module.finrank_fin_fun F)).symm i)
  simpa [f, Basis.reindex_apply] using this


theorem sign_pattern (h2 : (2 : F) ≠ 0) (m : Fin 4 → F) (hm : ∀ i, m i = 1 ∨ m i = -1)
    (hprod : ∏ i, m i = -1) :
    ∃ (ε : F) (p : Fin 4), (ε = 1 ∨ ε = -1) ∧ ∀ i, ε * m i = if i = p then -1 else 1 := by
  rw [Fin.prod_univ_four] at hprod
  rcases hm 0 with h0 | h0 <;> rcases hm 1 with h1 | h1 <;> rcases hm 2 with h2' | h2' <;>
    rcases hm 3 with h3 | h3 <;> rw [h0, h1, h2', h3] at hprod
  · exact absurd (by linear_combination hprod) h2
  · exact ⟨1, 3, Or.inl rfl, fun i => by fin_cases i <;> simp [h0, h1, h2', h3]⟩
  · exact ⟨1, 2, Or.inl rfl, fun i => by fin_cases i <;> simp [h0, h1, h2', h3]⟩
  · exact absurd (by linear_combination hprod) h2
  · exact ⟨1, 1, Or.inl rfl, fun i => by fin_cases i <;> simp [h0, h1, h2', h3]⟩
  · exact absurd (by linear_combination hprod) h2
  · exact absurd (by linear_combination hprod) h2
  · exact ⟨-1, 0, Or.inr rfl, fun i => by fin_cases i <;> simp [h0, h1, h2', h3]⟩
  · exact ⟨1, 0, Or.inl rfl, fun i => by fin_cases i <;> simp [h0, h1, h2', h3]⟩
  · exact absurd (by linear_combination hprod) h2
  · exact absurd (by linear_combination hprod) h2
  · exact ⟨-1, 1, Or.inr rfl, fun i => by fin_cases i <;> simp [h0, h1, h2', h3]⟩
  · exact absurd (by linear_combination hprod) h2
  · exact ⟨-1, 2, Or.inr rfl, fun i => by fin_cases i <;> simp [h0, h1, h2', h3]⟩
  · exact ⟨-1, 3, Or.inr rfl, fun i => by fin_cases i <;> simp [h0, h1, h2', h3]⟩
  · exact absurd (by linear_combination hprod) h2


theorem coe_eq_of_inv_mul_mul (P A : GL (Fin 4) F) {M : Matrix (Fin 4) (Fin 4) F}
    (h : ((P⁻¹ * A * P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = M) :
    (A : Matrix (Fin 4) (Fin 4) F) =
      (P : Matrix (Fin 4) (Fin 4) F) * M * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  have : A = P * (P⁻¹ * A * P) * P⁻¹ := by group
  rw [this, Units.val_mul, Units.val_mul, h]

theorem det_inv_mul_mul (P A : GL (Fin 4) F) :
    ((P⁻¹ * A * P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det =
      (A : Matrix (Fin 4) (Fin 4) F).det := by
  have := Matrix.det_units_conj P⁻¹ (A : Matrix (Fin 4) (Fin 4) F)
  simpa using this

theorem exists_diag_frame_lin {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0)
    (ρ : Fin 4 → GL (Fin 4) F) (hρ2 : ∀ j, ρ j * ρ j = 1)
    (hdet : ∀ j, ((ρ j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = -1)
    (hcomm : ∀ j k, ∃ c : F,
      ((ρ j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          ((ρ k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        c • (((ρ k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          ((ρ j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)))
    (hne : ∀ j k, j ≠ k → ∀ c : F,
      ((ρ j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) ≠
        c • ((ρ k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) :
    ∃ (P : GL (Fin 4) F) (ε : Fin 4 → F), (∀ j, ε j = 1 ∨ ε j = -1) ∧
      ∀ j, ((P⁻¹ * ρ j * P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        ε j • ((reflDiag F j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  classical
  have hcomm' : ∀ j k, (ρ j : Matrix (Fin 4) (Fin 4) F) * ρ k =
      (ρ k : Matrix (Fin 4) (Fin 4) F) * ρ j := fun j k => by
    obtain ⟨c, hc⟩ := hcomm j k
    exact mul_comm_of_smul h2 (hρ2 j) (hρ2 k) (hdet j) hc
  obtain ⟨b, μ, hb⟩ := exists_common_eigenbasis_lin h2 ρ hρ2 hcomm'
  have hdiag : ∀ j, ((basisGL b)⁻¹ * ρ j * basisGL b : GL (Fin 4) F) =
      (diagonal (μ j) : Matrix (Fin 4) (Fin 4) F) := fun j => basisGL_conj b (ρ j) (μ j) (hb j)
  have hsign : ∀ j i, μ j i = 1 ∨ μ j i = -1 := by
    intro j i
    have h1 : ((basisGL b)⁻¹ * ρ j * basisGL b) * ((basisGL b)⁻¹ * ρ j * basisGL b) = 1 := by
      calc ((basisGL b)⁻¹ * ρ j * basisGL b) * ((basisGL b)⁻¹ * ρ j * basisGL b)
          = (basisGL b)⁻¹ * (ρ j * ρ j) * basisGL b := by group
        _ = 1 := by rw [hρ2 j]; group
    have h3 : (diagonal (μ j) * diagonal (μ j) : Matrix (Fin 4) (Fin 4) F) = 1 := by
      rw [← hdiag j, ← Units.val_mul, h1, Units.val_one]
    rw [diagonal_mul_diagonal] at h3
    have h4 := congrFun (congrFun h3 i) i
    simp only [diagonal_apply_eq, Matrix.one_apply_eq] at h4
    exact mul_self_eq_one_iff.1 h4
  have hprod : ∀ j, ∏ i, μ j i = -1 := by
    intro j
    rw [← det_diagonal, ← hdiag j, det_inv_mul_mul, hdet j]
  choose ε p hε hp using fun j => sign_pattern h2 (μ j) (hsign j) (hprod j)
  have hεε : ∀ j, ε j * ε j = 1 := fun j => by
    rcases hε j with h | h <;> rw [h] <;> norm_num
  have hμ : ∀ j i, μ j i = ε j * (if i = p j then -1 else 1) := fun j i => by
    rw [← hp j i, ← mul_assoc, hεε j, one_mul]
  have hinj : Function.Injective p := by
    intro j k hjk
    by_contra hne'
    have hX : ∀ l, (ρ l : Matrix (Fin 4) (Fin 4) F) = ε l • ((basisGL b : Matrix (Fin 4) (Fin 4) F) *
        reflDiagMat F (p l) * ((basisGL b)⁻¹ : GL (Fin 4) F)) := fun l => by
      rw [coe_eq_of_inv_mul_mul (basisGL b) (ρ l) (hdiag l)]
      have : (diagonal (μ l) : Matrix (Fin 4) (Fin 4) F) = ε l • reflDiagMat F (p l) := by
        unfold reflDiagMat
        ext a c
        simp only [diagonal_apply, Matrix.smul_apply, hμ, smul_eq_mul]
        by_cases hac : a = c
        · subst hac
          simp
        · simp [hac]
      rw [this, Matrix.mul_smul, Matrix.smul_mul]
    apply hne j k hne' (ε j * ε k)
    rw [hX j, hX k, hjk, smul_smul, mul_assoc (ε j) (ε k) (ε k), hεε k, mul_one]
  let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective p (Finite.injective_iff_bijective.1 hinj)
  have hσ : ∀ i, σ i = p i := fun i => rfl
  let c : Basis (Fin 4) F (Fin 4 → F) := b.reindex σ.symm
  have hc : ∀ j i, (ρ j : Matrix (Fin 4) (Fin 4) F) *ᵥ c i = μ j (σ i) • c i := fun j i => by
    simp only [c, Basis.reindex_apply, Equiv.symm_symm]
    exact hb j (σ i)
  have hμσ : ∀ j i, μ j (σ i) = ε j * (if i = j then -1 else 1) := by
    intro j i
    rw [hμ j (σ i)]
    have hiff : σ i = p j ↔ i = j := by
      rw [← hσ j]
      exact σ.injective.eq_iff
    simp only [hiff]
  refine ⟨basisGL c, ε, hε, fun j => ?_⟩
  rw [basisGL_conj c (ρ j) (fun i => μ j (σ i)) (hc j)]
  change _ = ε j • reflDiagMat F j
  unfold reflDiagMat
  ext a d
  simp only [diagonal_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases had : a = d
  · subst had
    simp only [↓reduceIte]
    exact hμσ j a
  · simp [had]


theorem exists_diag_frame_lin_perm {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0)
    (ρ : Fin 4 → GL (Fin 4) F) (hρ2 : ∀ j, ρ j * ρ j = 1)
    (hdet : ∀ j, ((ρ j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = -1)
    (hcomm : ∀ j k, ∃ c : F,
      ((ρ j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          ((ρ k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        c • (((ρ k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          ((ρ j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)))
    (hne : ∀ j k, j ≠ k → ∀ c : F,
      ((ρ j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) ≠
        c • ((ρ k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) :
    ∃ (P : GL (Fin 4) F) (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → F), (∀ j, ε j = 1 ∨ ε j = -1) ∧
      ∀ j, ((P⁻¹ * ρ j * P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        ε j • ((reflDiag F (σ j) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  obtain ⟨P, ε, hε, h⟩ := exists_diag_frame_lin h2 ρ hρ2 hdet hcomm hne
  exact ⟨P, 1, ε, hε, h⟩

end CFSG.GH74.Generic.S1
