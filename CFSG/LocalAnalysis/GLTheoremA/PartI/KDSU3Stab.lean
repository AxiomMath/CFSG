module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag Matrix

variable {n : ℕ} {K : Type} [Field K]

private def jMat (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

private lemma jMat_mul_self : jMat K * jMat K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jMat, Matrix.mul_apply, Fin.sum_univ_three]

private lemma stab_core (h : UnitaryFieldData 2 n K) [CharP K 2] (R A : Matrix (Fin 3) (Fin 3) K)
    (α : K)
    (hR : (R.map h.bar)ᵀ * R = jMat K) (hA : (A.map h.bar)ᵀ * A = 1)
    (hAw : A *ᵥ (R *ᵥ Pi.single 0 1) = α • (R *ᵥ Pi.single 0 1)) (hα : α ≠ 0)
    (hdet : A.det * h.bar α = α ^ 2) :
    h.norm α = 1 ∧ A ^ 4 = Matrix.scalar (Fin 3) (α ^ 4) := by
  set Rinv := jMat K * (R.map h.bar)ᵀ with hRinv_def
  have hRinv : Rinv * R = 1 := by
    rw [hRinv_def, Matrix.mul_assoc, hR, jMat_mul_self]
  have hRinv' : R * Rinv = 1 := mul_eq_one_comm.mp hRinv
  set B := Rinv * A * R with hB
  have hAR : A * R = R * B := by
    rw [hB, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hRinv', Matrix.one_mul]
  have hBe : B *ᵥ Pi.single 0 1 = α • Pi.single 0 1 := by
    rw [hB, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hAw, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, hRinv, Matrix.one_mulVec]
  have hBJ : (B.map h.bar)ᵀ * jMat K * B = jMat K := by
    calc (B.map h.bar)ᵀ * jMat K * B = (B.map h.bar)ᵀ * ((R.map h.bar)ᵀ * 1 * R) * B := by
          rw [Matrix.mul_one, hR]
      _ = ((R * B).map h.bar)ᵀ * 1 * (R * B) := (conjTranspose_mul_mul h 1 R B).symm
      _ = ((A * R).map h.bar)ᵀ * 1 * (A * R) := by rw [hAR]
      _ = (R.map h.bar)ᵀ * ((A.map h.bar)ᵀ * 1 * A) * R := conjTranspose_mul_mul h 1 A R
      _ = jMat K := by rw [Matrix.mul_one, hA, Matrix.mul_one, hR]
  have hB00 : B 0 0 = α := by
    have := congrFun hBe 0
    simpa [Matrix.mulVec_single_one] using this
  have hB10 : B 1 0 = 0 := by
    have := congrFun hBe 1
    simpa [Matrix.mulVec_single_one] using this
  have hB20 : B 2 0 = 0 := by
    have := congrFun hBe 2
    simpa [Matrix.mulVec_single_one] using this
  have e01 := congrFun (congrFun hBJ 0) 1
  have e02 := congrFun (congrFun hBJ 0) 2
  have e11 := congrFun (congrFun hBJ 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, jMat, hB00, hB10, hB20] at e01 e02 e11
  have hB21 : B 2 1 = 0 := e01.resolve_left hα
  simp [hB21] at e11
  have hdetR : R.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hRinv
    rw [det_mul, h0, mul_zero, det_one] at this
    exact zero_ne_one this
  have hdetAB : A.det = B.det := by
    have := congrArg Matrix.det hAR
    rw [det_mul, det_mul, mul_comm] at this
    exact mul_left_cancel₀ hdetR this
  have hdetB : B.det = α * B 1 1 * B 2 2 := by
    rw [det_fin_three]
    simp [hB00, hB10, hB20, hB21]
  rw [hdetAB, hdetB] at hdet
  have hB11 : B 1 1 = α := by
    refine mul_left_cancel₀ hα ?_
    linear_combination hdet - α * B 1 1 * e02
  rw [hB11] at e11
  have hn : h.norm α = 1 := by
    unfold UnitaryFieldData.norm
    linear_combination e11
  have hB22 : B 2 2 = α := by
    unfold UnitaryFieldData.norm at hn
    linear_combination α * e02 - B 2 2 * hn
  refine ⟨hn, ?_⟩
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hBB : B * B = !![α ^ 2, 0, B 0 1 * B 1 2; 0, α ^ 2, 0; 0, 0, α ^ 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, hB00, hB10, hB20, hB21, hB11, hB22] <;>
      first | linear_combination | linear_combination (α * B 0 1) * h2 |
        linear_combination (α * B 0 2) * h2 | linear_combination (α * B 1 2) * h2
  have hB4 : B ^ 4 = Matrix.scalar (Fin 3) (α ^ 4) := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sq, sq, hBB]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply] <;>
      first | linear_combination | linear_combination (α ^ 2 * B 0 1 * B 1 2) * h2
  have h4 : R * B ^ 4 = A ^ 4 * R := (SemiconjBy.pow_right (hAR.symm : SemiconjBy R B A) 4).eq
  calc A ^ 4 = A ^ 4 * R * Rinv := by rw [Matrix.mul_assoc, hRinv', Matrix.mul_one]
    _ = R * B ^ 4 * Rinv := by rw [h4]
    _ = Matrix.scalar (Fin 3) (α ^ 4) := by
      rw [hB4, ← (Matrix.scalar_commute (α ^ 4) (fun _ => Commute.all _ _) R).eq,
        Matrix.mul_assoc, hRinv', Matrix.mul_one]

private lemma exists_witt_matrix (h : UnitaryFieldData 2 n K) (w : Fin 3 → K) (hw0 : w ≠ 0)
    (hw : gramForm h (1 : Matrix (Fin 3) (Fin 3) K) w w = 0) :
    ∃ R : Matrix (Fin 3) (Fin 3) K, (R.map h.bar)ᵀ * R = jMat K ∧
      R *ᵥ Pi.single 0 1 = w := by
  have hB : (gramForm h (1 : Matrix (Fin 3) (Fin 3) K)).IsSymm := gramForm_isSymm h (by simp)
  have hBl : (gramForm h (1 : Matrix (Fin 3) (Fin 3) K)).SeparatingLeft :=
    gramForm_separatingLeft h (by simp)
  have hn : Module.finrank K (Fin 3 → K) = 2 * 1 + 1 := by simp
  obtain ⟨⟨b, hab, hbb⟩, -⟩ := CFSG.LinearGroups.hermitian_hyperbolic_splitting h hB hBl hw0 hw
  obtain ⟨bas, hbas, ha, -⟩ := exists_hypBasis_of_pair h hB hBl hn (r := 1) (ε := 1)
    (by norm_num) hw hbb hab
  let v : Fin 3 → (Fin 3 → K) :=
    ![bas (.inl ⟨0, by norm_num⟩), bas (.inr (.inl 0)), bas (.inr (.inr ⟨0, by norm_num⟩))]
  have key : ∀ i j, (((Matrix.of fun i j => v j i).map h.bar)ᵀ * (Matrix.of fun i j => v j i)) i j =
      gramForm h (1 : Matrix (Fin 3) (Fin 3) K) (v i) (v j) := by
    intro i j
    simp [Matrix.mul_apply, gramForm_apply, dotProduct]
  refine ⟨Matrix.of fun i j => v j i, ?_, ?_⟩
  · ext i j
    rw [key]
    fin_cases i <;> fin_cases j <;> simp [v, hbas, jMat]
  · have ha' : bas (.inl 0) = w := ha
    rw [Matrix.mulVec_single_one]
    funext i
    simp [Matrix.col_apply, v, ha']

private def stabSub (h : UnitaryFieldData 2 n K) (w : Fin 3 → K) : Subgroup (GL (Fin 3) K) where
  carrier := {A | A ∈ primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ∧
    ∃ μ : K, (A : Matrix (Fin 3) (Fin 3) K) *ᵥ w = μ • w}
  mul_mem' := by
    rintro A B ⟨hA, μ, hμ⟩ ⟨hB, ν, hν⟩
    refine ⟨mul_mem hA hB, ν * μ, ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hν, Matrix.mulVec_smul, hμ, smul_smul]
  one_mem' := ⟨one_mem _, 1, by simp⟩
  inv_mem' := by
    rintro A ⟨hA, μ, hμ⟩
    refine ⟨inv_mem hA, μ⁻¹, ?_⟩
    have h1 : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [hμ, Matrix.mulVec_smul] at h1
    by_cases hμ0 : μ = 0
    · subst hμ0
      rw [zero_smul] at h1
      subst h1
      simp
    · calc ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w
          = μ⁻¹ • μ • (((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) := by
            rw [smul_smul, inv_mul_cancel₀ hμ0, one_smul]
        _ = μ⁻¹ • w := by rw [h1]

private lemma mem_stabSub {h : UnitaryFieldData 2 n K} {w : Fin 3 → K} {A : GL (Fin 3) K} :
    A ∈ stabSub h w ↔
      A ∈ primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ∧
        ∃ μ : K, (A : Matrix (Fin 3) (Fin 3) K) *ᵥ w = μ • w :=
  Iff.rfl

private noncomputable def eigval (h : UnitaryFieldData 2 n K) (w : Fin 3 → K)
    (A : stabSub h w) : K :=
  Classical.choose (mem_stabSub.mp A.2).2

private lemma eigval_spec (h : UnitaryFieldData 2 n K) (w : Fin 3 → K) (A : stabSub h w) :
    ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w = eigval h w A • w :=
  Classical.choose_spec (mem_stabSub.mp A.2).2

private lemma eigval_unique {h : UnitaryFieldData 2 n K} {w : Fin 3 → K} (hw0 : w ≠ 0)
    {A : stabSub h w} {μ : K}
    (hμ : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w = μ • w) : eigval h w A = μ :=
  smul_left_injective K hw0 ((eigval_spec h w A).symm.trans hμ)

private lemma eigval_ne_zero {h : UnitaryFieldData 2 n K} {w : Fin 3 → K} (hw0 : w ≠ 0)
    (A : stabSub h w) : eigval h w A ≠ 0 := by
  intro h0
  have h1 := eigval_spec h w A
  rw [h0, zero_smul] at h1
  apply hw0
  have h2 : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  rw [h1, Matrix.mulVec_zero] at h2
  exact h2.symm

private lemma eigval_mul {h : UnitaryFieldData 2 n K} {w : Fin 3 → K} (hw0 : w ≠ 0)
    (A B : stabSub h w) : eigval h w (A * B) = eigval h w A * eigval h w B := by
  refine eigval_unique hw0 ?_
  rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, eigval_spec h w B,
    Matrix.mulVec_smul, eigval_spec h w A, smul_smul, mul_comm]

private noncomputable def eigHom (h : UnitaryFieldData 2 n K) {w : Fin 3 → K} (hw0 : w ≠ 0) :
    stabSub h w →* Kˣ :=
  MonoidHom.mk' (fun A => Units.mk0 (eigval h w A) (eigval_ne_zero hw0 A)) (fun A B => by
    refine Units.ext ?_
    simp [eigval_mul hw0])

private noncomputable def psiHom (h : UnitaryFieldData 2 n K) {w : Fin 3 → K} (hw0 : w ≠ 0) :
    stabSub h w →* Kˣ :=
  eigHom h hw0 ^ 2 * ((Units.map h.bar.toMonoidHom).comp (eigHom h hw0))⁻¹ *
    (Matrix.GeneralLinearGroup.det.comp (stabSub h w).subtype)⁻¹

private lemma psiHom_apply (h : UnitaryFieldData 2 n K) {w : Fin 3 → K} (hw0 : w ≠ 0)
    (A : stabSub h w) : psiHom h hw0 A = (eigHom h hw0 A) ^ 2 *
      (Units.map h.bar.toMonoidHom (eigHom h hw0 A))⁻¹ *
        (Matrix.GeneralLinearGroup.det (A : GL (Fin 3) K))⁻¹ := rfl

private lemma scalar_mulVec_eq (c : K) (w : Fin 3 → K) : Matrix.scalar (Fin 3) c *ᵥ w = c • w := by
  ext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

private lemma coe_eigHom (h : UnitaryFieldData 2 n K) {w : Fin 3 → K} (hw0 : w ≠ 0)
    (A : stabSub h w) : ((eigHom h hw0 A : Kˣ) : K) = eigval h w A := rfl

theorem exists_stabilizer_hom (h : UnitaryFieldData 2 n K) (w : Fin 3 → K) (hw0 : w ≠ 0)
    (hw : gramForm h (1 : Matrix (Fin 3) (Fin 3) K) w w = 0) :
    ∃ (St : Subgroup (GL (Fin 3) K)) (ψ : St →* Kˣ),
      (∀ A : GL (Fin 3) K, A ∈ St ↔
        (A ∈ primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ∧
          ∃ μ : K, (A : Matrix (Fin 3) (Fin 3) K) *ᵥ w = μ • w)) ∧
      (∀ c : Kˣ, h.norm (c : K) = 1 →
        ∃ hs : GeneralLinearGroup.scalar (Fin 3) c ∈ St,
          ψ ⟨GeneralLinearGroup.scalar (Fin 3) c, hs⟩ = 1) ∧
      (∀ A : St, ψ A = 1 → ∃ ν : Kˣ, h.norm (ν : K) = 1 ∧
        (A : GL (Fin 3) K) ^ 4 = GeneralLinearGroup.scalar (Fin 3) (ν ^ 4)) := by
  have := h.finite
  have := h.charP
  refine ⟨stabSub h w, psiHom h hw0, fun A => Iff.rfl, ?_, ?_⟩
  · intro c hc
    have hs : GeneralLinearGroup.scalar (Fin 3) c ∈ stabSub h w := by
      refine ⟨?_, c, ?_⟩
      · rw [mem_primeFormUnitary, GeneralLinearGroup.coe_scalar, scalar_barTranspose_mul_mul, hc,
          one_smul]
      · rw [GeneralLinearGroup.coe_scalar, scalar_mulVec_eq]
    refine ⟨hs, ?_⟩
    have hev : eigval h w ⟨GeneralLinearGroup.scalar (Fin 3) c, hs⟩ = c := by
      refine eigval_unique hw0 ?_
      rw [GeneralLinearGroup.coe_scalar, scalar_mulVec_eq]
    have heig : eigHom h hw0 ⟨GeneralLinearGroup.scalar (Fin 3) c, hs⟩ = c :=
      Units.ext (by rw [coe_eigHom, hev])
    have hdetc : Matrix.GeneralLinearGroup.det
        ((⟨GeneralLinearGroup.scalar (Fin 3) c, hs⟩ : stabSub h w) : GL (Fin 3) K) = c ^ 3 := by
      rw [Subgroup.coe_mk, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
    apply Units.ext
    rw [psiHom_apply, heig, hdetc]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.coe_map,
      Units.val_one, MonoidHom.coe_coe]
    have hcne : (c : K) ≠ 0 := c.ne_zero
    have hbar : h.bar (c : K) ≠ 0 := by
      intro h0
      rw [UnitaryFieldData.norm, h0, mul_zero] at hc
      exact zero_ne_one hc
    field_simp
    exact hc.symm
  · intro A hA
    have hα := eigval_ne_zero hw0 A
    have hψ := congrArg Units.val hA
    rw [psiHom_apply] at hψ
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.coe_map,
      Units.val_one, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, coe_eigHom,
      Matrix.GeneralLinearGroup.val_det_apply] at hψ
    have hdA : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
      Matrix.GeneralLinearGroup.det_ne_zero _
    have hbar : h.bar (eigval h w A) ≠ 0 := by simpa using hα
    field_simp at hψ
    have hdet : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det * h.bar (eigval h w A) =
        eigval h w A ^ 2 := by
      first | linear_combination -hψ | linear_combination hψ
    obtain ⟨R, hR, hRw⟩ := exists_witt_matrix h w hw0 hw
    have hAw : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (R *ᵥ Pi.single 0 1) =
        eigval h w A • (R *ᵥ Pi.single 0 1) := by
      rw [hRw]
      exact eigval_spec h w A
    have hAu : (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
        ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      have := mem_primeFormUnitary.mp (mem_stabSub.mp A.2).1
      rwa [Units.val_one, Matrix.mul_one] at this
    obtain ⟨hn, h4⟩ := stab_core h R _ _ hR hAu hAw hα hdet
    refine ⟨Units.mk0 _ hα, hn, Units.ext ?_⟩
    rw [Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar, Units.val_pow_eq_pow_val,
      Units.val_mk0]
    exact h4

end CFSG.LocalAnalysis.GLTheoremA
