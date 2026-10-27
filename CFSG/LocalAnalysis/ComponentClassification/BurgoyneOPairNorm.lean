module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOPairMat

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Polynomial

variable {K : Type} [Field K] {n : ℕ}

theorem nondeg_of_GL {d : ℕ} (R : GL (Fin d) K) :
    ∀ v, (∀ w, v ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ w = 0) → v = 0 := by
  intro v hv
  have h1 : v ᵥ* (R : Matrix (Fin d) (Fin d) K) = 0 := by
    funext j
    have := hv (Pi.single j 1)
    rw [dotProduct_mulVec, dotProduct_single, mul_one] at this
    exact this
  have h2 : (v ᵥ* (R : Matrix (Fin d) (Fin d) K)) ᵥ* ((R⁻¹ : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = v := by
    rw [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
  rw [← h2, h1, zero_vecMul]

theorem exists_sq_sub_mul_sq [Finite K] (hK : ringChar K ≠ 2) {c : K} (hc : c ≠ 0) (t : K) :
    ∃ α β : K, α ^ 2 - c * β ^ 2 = t := by
  have : Fintype K := Fintype.ofFinite K
  have hodd : Fintype.card K % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp (CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK)
  have hg : degree (-(C c) * X ^ 2 - C t : K[X]) = 2 := by
    rw [sub_eq_add_neg, ← C_neg, ← C_neg]
    rw [degree_add_eq_left_of_degree_lt]
    · rw [degree_C_mul_X_pow 2 (neg_ne_zero.2 hc)]
      rfl
    · rw [degree_C_mul_X_pow 2 (neg_ne_zero.2 hc)]
      exact lt_of_le_of_lt degree_C_le (by decide)
  obtain ⟨α, β, h⟩ := FiniteField.exists_root_sum_quadratic (f := X ^ 2)
    (g := -(C c) * X ^ 2 - C t) (degree_X_pow 2) hg hodd
  refine ⟨α, β, ?_⟩
  simp only [eval_pow, eval_X, eval_sub, eval_mul, eval_neg, eval_C] at h
  linear_combination h

section Planes

variable {d : ℕ} {R A : Matrix (Fin d) (Fin d) K} {c ε : K}

theorem plGram_apply (v : Fin d → K) :
    plGram R A v = !![v ⬝ᵥ R *ᵥ v, v ⬝ᵥ R *ᵥ (A *ᵥ v);
      (A *ᵥ v) ⬝ᵥ R *ᵥ v, (A *ᵥ v) ⬝ᵥ R *ᵥ (A *ᵥ v)] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [plGram, plVec]

theorem plGram_of_anti (h2 : (2 : K) ≠ 0) (hR : Rᵀ = R) (hA2 : A * A = c • 1)
    (hAR : Aᵀ * R = (-1 : K) • (R * A)) (v : Fin d → K) :
    v ⬝ᵥ R *ᵥ (A *ᵥ v) = 0 ∧ (A *ᵥ v) ⬝ᵥ R *ᵥ v = 0 ∧
      (A *ᵥ v) ⬝ᵥ R *ᵥ (A *ᵥ v) = -c * (v ⬝ᵥ R *ᵥ v) := by
  have e1 := dot_adj hAR v v
  rw [dot_symm hR] at e1
  have hb : v ⬝ᵥ R *ᵥ (A *ᵥ v) = 0 := by
    have : (2 : K) * (v ⬝ᵥ R *ᵥ (A *ᵥ v)) = 0 := by linear_combination e1
    exact (mul_eq_zero.1 this).resolve_left h2
  refine ⟨hb, by rw [dot_symm hR]; exact hb, ?_⟩
  rw [dot_adj hAR, mulVec_mulVec_self hA2, mulVec_smul, dotProduct_smul, smul_eq_mul]
  ring

theorem plGram_of_sym (hR : Rᵀ = R) (hA2 : A * A = c • 1) (hAR : Aᵀ * R = (1 : K) • (R * A))
    (v : Fin d → K) :
    (A *ᵥ v) ⬝ᵥ R *ᵥ v = v ⬝ᵥ R *ᵥ (A *ᵥ v) ∧
      (A *ᵥ v) ⬝ᵥ R *ᵥ (A *ᵥ v) = c * (v ⬝ᵥ R *ᵥ v) := by
  refine ⟨dot_symm hR _ _, ?_⟩
  rw [dot_adj hAR, mulVec_mulVec_self hA2, mulVec_smul, dotProduct_smul, smul_eq_mul]
  ring

theorem PairFam.lin (hR : Rᵀ = R) (hA2 : A * A = c • 1) (hAR : Aᵀ * R = ε • (R * A))
    {k : ℕ} {u : Fin k → Fin d → K} (hu : PairFam R A u) (α β : Fin k → K)
    (hne : ∀ i, (α i • u i + β i • A *ᵥ u i) ⬝ᵥ R *ᵥ (α i • u i + β i • A *ᵥ u i) ≠ 0) :
    PairFam R A fun i => α i • u i + β i • A *ᵥ u i := by
  have hAA : ∀ i j, i ≠ j → (A *ᵥ u i) ⬝ᵥ R *ᵥ (A *ᵥ u j) = 0 := by
    intro i j hij
    rw [dot_adj hAR, mulVec_mulVec_self hA2, mulVec_smul, dotProduct_smul, smul_eq_mul,
      hu.orth i j hij, mul_zero, mul_zero]
  have hAu : ∀ i j, i ≠ j → (A *ᵥ u i) ⬝ᵥ R *ᵥ u j = 0 := by
    intro i j hij
    rw [dot_symm hR, hu.orthA j i (Ne.symm hij)]
  refine ⟨hne, fun i j hij => ?_, fun i j hij => ?_⟩
  · simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, hu.orth i j hij, hu.orthA i j hij, hAu i j hij, hAA i j hij,
      mul_zero, add_zero]
  · simp only [mulVec_add, mulVec_smul, mulVec_mulVec_self hA2, dotProduct_add, add_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul, hu.orth i j hij, hu.orthA i j hij,
      hAu i j hij, hAA i j hij, mul_zero, add_zero]

end Planes

variable [Finite K]

theorem exists_pc_basis (hK : ringChar K ≠ 2) {R : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R)
    {A : Matrix (Fin (2 * n)) (Fin (2 * n)) K} {c : K} (hc : c ≠ 0) (hA2 : A * A = c • 1)
    (hAR : Aᵀ * R = (-1 : K) • ((R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * A))
    (s : Fin n → K) (hs : ∀ i, s i ≠ 0) :
    ∃ H : GL (Fin (2 * n)) K,
      (H : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R * H =
        blkEquiv K n (diagonal fun i => s i • wMat 1 (-c)) ∧
      A * H = H * blkDiag n (jMat c) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set Rm := (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) with hRm
  have hpair : ∀ u, u ⬝ᵥ Rm *ᵥ u ≠ 0 →
      (u ⬝ᵥ Rm *ᵥ u) * ((A *ᵥ u) ⬝ᵥ Rm *ᵥ (A *ᵥ u)) - (u ⬝ᵥ Rm *ᵥ (A *ᵥ u)) ^ 2 ≠ 0 := by
    intro u hu
    obtain ⟨hb, -, he⟩ := plGram_of_anti h2 hR hA2 hAR u
    rw [hb, he]
    intro h0
    have : -c * (u ⬝ᵥ Rm *ᵥ u) ^ 2 = 0 := by linear_combination h0
    rcases mul_eq_zero.1 this with h | h
    · exact hc (neg_eq_zero.1 h)
    · exact hu (pow_eq_zero_iff (by norm_num) |>.1 h)
  obtain ⟨u, hu⟩ := exists_pairFam h2 hR (nondeg_of_GL R) hA2 hAR (by norm_num) hpair n le_rfl
  have hex : ∀ i, ∃ αβ : K × K, αβ.1 ^ 2 - c * αβ.2 ^ 2 = s i / (u i ⬝ᵥ Rm *ᵥ u i) := by
    intro i
    obtain ⟨α, β, h⟩ := exists_sq_sub_mul_sq hK hc (s i / (u i ⬝ᵥ Rm *ᵥ u i))
    exact ⟨(α, β), h⟩
  choose αβ hαβ using hex
  have hnorm : ∀ i, ((αβ i).1 • u i + (αβ i).2 • A *ᵥ u i) ⬝ᵥ Rm *ᵥ
      ((αβ i).1 • u i + (αβ i).2 • A *ᵥ u i) = s i := by
    intro i
    obtain ⟨hb, hb', he⟩ := plGram_of_anti h2 hR hA2 hAR (u i)
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, hb, hb', he]
    have hαβ' := hαβ i
    have hne := hu.ne i
    field_simp at hαβ'
    linear_combination hαβ'
  set u' := fun i => (αβ i).1 • u i + (αβ i).2 • A *ᵥ u i with hu'
  have hu'f : PairFam Rm A u' :=
    hu.lin hR hA2 hAR (fun i => (αβ i).1) (fun i => (αβ i).2) fun i => by rw [hnorm]; exact hs i
  have hgram : ∀ i, plGram Rm A (u' i) = s i • wMat 1 (-c) := by
    intro i
    obtain ⟨hb, hb', he⟩ := plGram_of_anti h2 hR hA2 hAR (u' i)
    rw [plGram_apply, hb, hb', he, hu', hnorm]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [wMat]
    ring
  have hdet : (pairMat A u').det ≠ 0 := by
    refine pairMat_det_ne_zero hR hA2 hAR hu'f fun i => ?_
    rw [hgram, det_smul, wMat, det_diagonal]
    simp [hs i, hc]
  refine ⟨Matrix.nonsingInvUnit _ (isUnit_iff_ne_zero.2 hdet), ?_, mul_pairMat hA2 u'⟩
  change (pairMat A u')ᵀ * Rm * pairMat A u' = _
  rw [pairMat_gram_eq hR hA2 hAR hu'f]
  congr 2
  funext i
  exact hgram i

omit [Finite K] in
theorem exists_orth2_basis (hK : ringChar K ≠ 2) {R : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R)
    {A : Matrix (Fin (2 * n)) (Fin (2 * n)) K} {c : K} (hc : ¬ IsSquare c) (hA2 : A * A = c • 1)
    (hAR : Aᵀ * R = (1 : K) • ((R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * A))
    [Fact (Irreducible (sqPoly c))] :
    ∃ (H : GL (Fin (2 * n)) K) (β : Fin n → EAlg c), (∀ i, β i ≠ 0) ∧
      (H : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R * H =
        blkDiag n (wMat 1 c) * resMat (phiE c).toRingHom n (diagonal β) ∧
      A * H = H * blkDiag n (jMat c) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hc0 : c ≠ 0 := fun h => hc ⟨0, by rw [h, mul_zero]⟩
  set Rm := (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) with hRm
  have hpair : ∀ u, u ⬝ᵥ Rm *ᵥ u ≠ 0 →
      (u ⬝ᵥ Rm *ᵥ u) * ((A *ᵥ u) ⬝ᵥ Rm *ᵥ (A *ᵥ u)) - (u ⬝ᵥ Rm *ᵥ (A *ᵥ u)) ^ 2 ≠ 0 := by
    intro u hu h0
    obtain ⟨-, he⟩ := plGram_of_sym hR hA2 hAR u
    rw [he] at h0
    apply hc
    refine ⟨(u ⬝ᵥ Rm *ᵥ (A *ᵥ u)) / (u ⬝ᵥ Rm *ᵥ u), ?_⟩
    field_simp
    linear_combination h0
  obtain ⟨u, hu⟩ := exists_pairFam h2 hR (nondeg_of_GL R) hA2 hAR (by norm_num) hpair n le_rfl
  set β : Fin n → EAlg c := fun i => algebraMap K (EAlg c) (u i ⬝ᵥ Rm *ᵥ u i) +
    algebraMap K (EAlg c) ((u i ⬝ᵥ Rm *ᵥ (A *ᵥ u i)) / c) * AdjoinRoot.root (sqPoly c) with hβ
  have hgram : ∀ i, plGram Rm A (u i) = wMat 1 c * phiE c (β i) := by
    intro i
    obtain ⟨hb, he⟩ := plGram_of_sym hR hA2 hAR (u i)
    rw [plGram_apply, hb, he, hβ, phiE_add_root, smul_add_smul_jMat]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [wMat, Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp
  have hβ0 : ∀ i, β i ≠ 0 := by
    intro i h0
    have e := congrArg (fun x => phiE c x 0 0) h0
    simp only [hβ, phiE_add_root, smul_add_smul_jMat, map_zero] at e
    exact hu.ne i (by simpa using e)
  have hdet : (pairMat A u).det ≠ 0 := by
    refine pairMat_det_ne_zero hR hA2 hAR hu fun i => ?_
    rw [plGram_det]
    obtain ⟨hb, he⟩ := plGram_of_sym hR hA2 hAR (u i)
    rw [hb, he, ← sq]
    have := hpair (u i) (hu.ne i)
    rw [he] at this
    exact this
  refine ⟨Matrix.nonsingInvUnit _ (isUnit_iff_ne_zero.2 hdet), β, hβ0, ?_, mul_pairMat hA2 u⟩
  change (pairMat A u)ᵀ * Rm * pairMat A u = _
  rw [pairMat_gram_eq hR hA2 hAR hu, blkDiag, resMat_eq, ← map_mul, diagonal_map (map_zero _),
    diagonal_mul_diagonal]
  congr 2
  funext i
  rw [hgram i]
  rfl

end CFSG.ComponentClassification.Burgoyne.O
