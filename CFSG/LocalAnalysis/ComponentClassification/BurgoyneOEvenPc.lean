module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEvenOrth2
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOPcSlice
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOUnitComp
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOAntiComp
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSliceNF
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSplitCases

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL)

variable {K : Type} [Field K]

theorem blkEquiv_diagonal_diagonal (n : ℕ) (v : Fin n → Fin 2 → K) :
    blkEquiv K n (diagonal fun i => diagonal (v i)) =
      diagonal fun p => v ((pairEquiv n).symm p).1 ((pairEquiv n).symm p).2 := by
  ext p q
  obtain ⟨⟨i, j⟩, rfl⟩ := (pairEquiv n).surjective p
  obtain ⟨⟨k, l⟩, rfl⟩ := (pairEquiv n).surjective q
  rw [blkEquiv_apply, diagonal_apply, diagonal_apply, Equiv.symm_apply_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
  by_cases hik : i = k
  · subst hik
    by_cases hjl : j = l <;> simp [hjl]
  · simp [hik]

theorem smul_wMat (s a b : K) : s • wMat a b = diagonal fun j => s * ![a, b] j := by
  ext i j
  rw [wMat, Matrix.smul_apply, diagonal_apply, diagonal_apply]
  split_ifs <;> simp

theorem transpose_jMat_mul_wMat (c : K) :
    (jMat c)ᵀ * wMat 1 (-c) = (-1 : K) • (wMat 1 (-c) * jMat c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jMat, wMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem inv_mul_lin_mul {d : ℕ} {S : GL (Fin d) K} {A : Matrix (Fin d) (Fin d) K}
    (h : A * S = S * A) (x y : K) :
    ((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (x • 1 + y • A) * S = x • 1 + y • A := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.smul_mul, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    inv_mul_mul_eq h]

variable [Finite K]

theorem pc_propAConclusion (hK : ringChar K ≠ 2) {ℓ e : ℕ} (hℓ : ℓ.Prime)
    (hKc : Nat.card K = ℓ ^ e) {n : ℕ} (hn : 4 ≤ n) {R : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R)
    (hker : OKer (oQ R)) {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (θ : GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived (oQ R)))
    {t : X} (hsurj : OSurjX θ t) {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1)
    (htg : socleAction θ t = oκ _ g) {c : K} (hc : c ≠ 0)
    (hA2 : (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g.val.left = c • 1)
    (hAR : (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R =
      (-1 : K) • ((R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g.val.left))
    {Y : Subgroup X} (hY : Y ≠ ⊥) (hYO : Y ≤ oddCentralizerCore t) : PropAConclusion X t Y := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set A₁ := blkDiag n (jMat c) with hA₁
  obtain ⟨H₁, hgram₁, hAH₁⟩ := exists_pc_basis hK hR hc hA2 hAR (fun _ => 1)
    (fun _ => one_ne_zero)
  obtain ⟨R₁, hR₁⟩ : ∃ R₁, R₁ = CatalogueBGraphForm.glTranspose (2 * n) K H₁ * R * H₁ :=
    ⟨_, rfl⟩
  have hgramR₁ : (H₁ : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R * H₁ = R₁ := by
    rw [hR₁]
    simp only [Units.val_mul, CatalogueBGraphForm.glTranspose_matrix]
  have hR₁m : (R₁ : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-c)) := by
    rw [← hgramR₁, hgram₁]
    simp only [one_smul]
    rfl
  obtain ⟨θ₁, g₁, hg₁1, hg₁l, htg₁, hker₁, hsurj₁, -, hinj₁, hB₁⟩ :=
    exists_model hker hsimple hnab θ hsurj hg1 htg hgramR₁
  have hg₁A : (g₁.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = A₁ := by
    rw [hg₁l, Units.val_mul, Units.val_mul]
    exact inv_mul_mul_eq hAH₁
  have hcd₁ : CompData ⁅isoCent R₁ g₁.val.left, isoCent R₁ g₁.val.left⁆ := by
    by_cases hsq : IsSquare c
    · obtain ⟨s, hs⟩ := hsq
      have hs0 : s ≠ 0 := by
        rintro rfl
        exact hc (by rw [hs, mul_zero])
      have hcs : c = s ^ 2 := by rw [hs, sq]
      exact compData_anti h2 hs0 (by omega) (by rw [hR₁m, hcs]) (by rw [hg₁A, hA₁, hcs])
    · exact compData_unit hK hsq hℓ hKc (by omega) hR₁m hg₁A
  by_cases hK3 : Nat.card K = 3
  · have hbot := pc_oddCoreIn_eq_bot_three hK hK3 (by omega) hc hR₁m hker₁ hinj₁ hB₁
      hg₁1 hg₁A hcd₁ ((hsurj₁.core hsimple hnab).of_eq htg₁)
    exact propAConclusion_of_socle hsimple hnab θ₁ hY hYO (Or.inl (by rw [htg₁]; exact hbot))
  have hK5 : 5 ≤ Nat.card K := by
    obtain ⟨k, hk⟩ := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
    have h1 := Finite.one_lt_card (α := K)
    omega
  have hdesc₁ : ∀ x ∈ oddCentralizerCore t, ∃ g' : similarityPairs (oQ R₁),
      socleAction θ₁ x = oκ _ g' ∧ g'.val.right = 1 ∧ ∃ α β : K,
        (g'.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = α • 1 + β • A₁ := by
    intro x hx
    have hmem : socleAction θ₁ x ∈ oddCoreIn (socleAction θ₁).range (oκ _ g₁) := by
      rw [← htg₁, ← map_oddCentralizerCore_of_injective (socleAction_injective hsimple hnab θ₁)]
      exact ⟨x, hx, rfl⟩
    obtain ⟨g', hg'⟩ := hsurj₁ x hx
    rw [hg'] at hmem
    obtain ⟨hr, α, β, hl⟩ := pc_core hK (by omega) hc hR₁m hker₁ hinj₁ hB₁ hg₁1 hg₁A hcd₁ hmem
    exact ⟨g', hg', hr, α, β, hl⟩
  set s₂ : Fin n → K := fun i => if (i : ℕ) = 1 then -1 else 1 with hs₂
  have hs₂0 : ∀ i, s₂ i ≠ 0 := fun i => by
    simp only [hs₂]
    split_ifs <;> simp
  have hR₁s : (R₁ : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R₁ := by
    rw [hR₁m, blkDiag_transpose, wMat_transpose]
  have hA₁2 : A₁ * A₁ = c • 1 := by
    rw [hA₁, blkDiag_mul, jMat_mul_self, blkDiag_smul, blkDiag_one']
  have hA₁R : A₁ᵀ * R₁ = (-1 : K) • ((R₁ : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * A₁) := by
    rw [hR₁m, hA₁, blkDiag_transpose, blkDiag_mul, blkDiag_mul, transpose_jMat_mul_wMat,
      blkDiag_smul]
  obtain ⟨S, hgramS, hAS⟩ := exists_pc_basis hK hR₁s hc hA₁2 hA₁R s₂ hs₂0
  set w₂ : Fin (2 * n) → K := fun p =>
    s₂ ((pairEquiv n).symm p).1 * ![1, -c] ((pairEquiv n).symm p).2 with hw₂
  have hw₂0 : ∀ p, w₂ p ≠ 0 := by
    intro p
    refine mul_ne_zero (hs₂0 _) ?_
    generalize ((pairEquiv n).symm p).2 = j
    fin_cases j <;> simp [hc]
  have hgramS' : (S : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R₁ * S = diagGL hw₂0 := by
    rw [hgramS, coe_diagGL]
    simp only [smul_wMat]
    rw [blkEquiv_diagonal_diagonal]
  obtain ⟨θ₂, g₂, hg₂1, hg₂l, htg₂, hker₂, -, htrans₂, hinj₂, hB₂⟩ :=
    exists_model hker₁ hsimple hnab θ₁ hsurj₁ hg₁1 htg₁ hgramS'
  have hg₂A : (g₂.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = A₁ := by
    rw [hg₂l, Units.val_mul, Units.val_mul, hg₁A]
    exact inv_mul_mul_eq hAS
  have hW : OSliceW (by omega : 4 ≤ 2 * n) w₂ 1 (-c) := by
    refine ⟨one_ne_zero, neg_ne_zero.2 hc, fun i => ?_⟩
    have hp : (pairEquiv n).symm ⟨i, by omega⟩ = (⟨i / 2, by omega⟩, ⟨i % 2, by omega⟩) := by
      rw [Equiv.symm_apply_eq]
      apply Fin.ext
      rw [pairEquiv_val]
      simp only
      omega
    simp only [hw₂, hp, hs₂]
    fin_cases i <;> simp [qW]
  have hcore₂ : ∀ y ∈ oddCoreIn (socleAction θ₂).range (oκ _ g₂),
      ∃ g' : similarityPairs (oQ (diagGL hw₂0)), y = oκ _ g' ∧ g'.val.right = 1 ∧
        ∃ x z : K, (g'.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = x • 1 + z • A₁ := by
    intro y hy
    rw [← htg₂, ← map_oddCentralizerCore_of_injective
      (socleAction_injective hsimple hnab θ₂)] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨g', hg', hr, α, β, hl⟩ := hdesc₁ x hx
    obtain ⟨gx', hgx', hr', hl'⟩ := htrans₂ x g' hg' hr
    refine ⟨gx', hgx', hr', α, β, ?_⟩
    rw [hl', Units.val_mul, Units.val_mul, hl]
    exact inv_mul_lin_mul hAS α β
  refine propAConclusion_of_socle hsimple hnab θ₂ hY hYO (Or.inr fun Y' hY' hY'O => ?_)
  rw [htg₂] at hY'O ⊢
  exact slice_pc_propAConclusionIn hK hK5 (by omega) hc hw₂0 hW hker₂ hinj₂ hB₂ hg₂1 hg₂A hcore₂
    hY' hY'O

end CFSG.ComponentClassification.Burgoyne.O
