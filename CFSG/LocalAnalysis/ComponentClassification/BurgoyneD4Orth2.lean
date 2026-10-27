module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEvenOrth2
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneD4Pc

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.D4

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank Polynomial
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.O

variable {K : Type} [Field K]

theorem det_blkDiagF {n : ℕ} (f : Fin n → Matrix (Fin 2) (Fin 2) K) :
    (blkDiagF f).det = ∏ i, (f i).det := by
  have e : blkDiagF f = Matrix.reindex ((Equiv.prodComm (Fin 2) (Fin n)).trans (pairEquiv n))
      ((Equiv.prodComm (Fin 2) (Fin n)).trans (pairEquiv n)) (blockDiagonal f) := by
    ext p q
    obtain ⟨⟨i, j⟩, rfl⟩ := (pairEquiv n).surjective p
    obtain ⟨⟨k, l⟩, rfl⟩ := (pairEquiv n).surjective q
    rw [blkDiagF_apply, reindex_apply, submatrix_apply]
    simp only [Equiv.symm_trans_apply, Equiv.symm_apply_apply, Equiv.prodComm_symm,
      Equiv.prodComm_apply, Prod.swap_prod_mk, blockDiagonal_apply]
  rw [e, det_reindex_self, det_blockDiagonal]

theorem isSquare_of_isSquare_det_phiE [Finite K] (hK : ringChar K ≠ 2) {c : K}
    (hc : ¬ IsSquare c) [Fact (Irreducible (sqPoly c))] {δ : EAlg c} (hδ : δ ≠ 0)
    (h : IsSquare (phiE c δ).det) : IsSquare δ := by
  have hc0 : c ≠ 0 := fun h0 => hc ⟨0, by rw [h0, mul_zero]⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨hEf, hE⟩ := finite_ringChar_EAlg hK hc0
  have : Fintype (EAlg c) := Fintype.ofFinite _
  set a := phiE c δ 0 0 with ha
  set b := phiE c δ 1 0 with hb
  have hδab := eq_add_root hc0 δ
  have hφ : phiE c δ = a • (1 : Matrix (Fin 2) (Fin 2) K) + b • jMat c := by
    conv_lhs => rw [hδab]
    exact phiE_add_root c a b
  have hdet : (phiE c δ).det = a ^ 2 - c * b ^ 2 := by
    rw [hφ, det_fin_two]
    simp [jMat]
    ring
  have key : (algebraMap K (EAlg c) a + algebraMap K (EAlg c) b * AdjoinRoot.root (sqPoly c)) ^
      (Nat.card K + 1) = algebraMap K (EAlg c) (a ^ 2 - c * b ^ 2) := by
    rw [pow_succ, pow_card_add_root hK hc, map_neg, map_sub, map_mul, map_pow, map_pow,
      ← root_sq]
    ring
  have hnorm : δ ^ (Nat.card K + 1) = algebraMap K (EAlg c) ((phiE c δ).det) := by
    rw [hdet, ← key, ← hδab]
  have hN0 : (phiE c δ).det ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hnorm
    exact hδ (pow_eq_zero_iff (by omega) |>.1 hnorm)
  have hN := (FiniteField.isSquare_iff hK hN0).1 h
  refine (FiniteField.isSquare_iff hE hδ).2 ?_
  obtain ⟨m, hm⟩ : Odd (Fintype.card K) := Nat.odd_iff.2 (FiniteField.odd_card_of_char_ne_two hK)
  have hcardE : Fintype.card (EAlg c) = (2 * m + 1) ^ 2 := by
    rw [← Nat.card_eq_fintype_card, card_EAlg hc0, Nat.card_eq_fintype_card, hm]
  have hhalf : Fintype.card (EAlg c) / 2 = (Nat.card K + 1) * (Fintype.card K / 2) := by
    rw [hcardE, Nat.card_eq_fintype_card, hm]
    have : (2 * m + 1) ^ 2 = 2 * ((2 * m + 1 + 1) * m) + 1 := by ring
    rw [this, Nat.mul_add_div (by norm_num), show (2 * m + 1) / 2 = m by omega]
    omega
  rw [hhalf, pow_mul, hnorm, ← map_pow, hN, map_one]

section TS

variable {c : K}

@[expose] def o2Blk (μ : Matrix (Fin 2) (Fin 2) K) (α β : K) (x : Fin 2 → Fin 2 → K) :
    Fin 4 → Fin 2 → K :=
  ![x 0, x 1, α • x 0 + β • x 1, μ *ᵥ (-β • x 0 + α • x 1)]

theorem o2Blk_add (μ : Matrix (Fin 2) (Fin 2) K) (α β : K) (x x' : Fin 2 → Fin 2 → K) :
    o2Blk μ α β (x + x') = o2Blk μ α β x + o2Blk μ α β x' := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · change α • (x 0 + x' 0) + β • (x 1 + x' 1) = (α • x 0 + β • x 1) + (α • x' 0 + β • x' 1)
    module
  · change μ *ᵥ (-β • (x 0 + x' 0) + α • (x 1 + x' 1)) =
      μ *ᵥ (-β • x 0 + α • x 1) + μ *ᵥ (-β • x' 0 + α • x' 1)
    rw [← mulVec_add]
    congr 1
    module

theorem o2Blk_smul (μ : Matrix (Fin 2) (Fin 2) K) (α β a : K) (x : Fin 2 → Fin 2 → K) :
    o2Blk μ α β (a • x) = a • o2Blk μ α β x := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · change α • (a • x 0) + β • (a • x 1) = a • (α • x 0 + β • x 1)
    module
  · change μ *ᵥ (-β • (a • x 0) + α • (a • x 1)) = a • μ *ᵥ (-β • x 0 + α • x 1)
    rw [← mulVec_smul]
    congr 1
    module

@[expose] def o2Map (μ : Matrix (Fin 2) (Fin 2) K) (α β : K) :
    (Fin 2 → Fin 2 → K) →ₗ[K] (Fin (2 * 4) → K) where
  toFun x := blkVec (o2Blk μ α β x)
  map_add' x x' := by rw [o2Blk_add]; rfl
  map_smul' a x := by rw [o2Blk_smul]; rfl

theorem o2Map_apply (μ : Matrix (Fin 2) (Fin 2) K) (α β : K) (x : Fin 2 → Fin 2 → K) :
    o2Map μ α β x = blkVec (o2Blk μ α β x) := rfl

theorem o2Map_injective (μ : Matrix (Fin 2) (Fin 2) K) (α β : K) :
    Function.Injective (o2Map μ α β) := by
  intro x x' h
  have h0 := congrArg blkOf h
  rw [o2Map_apply, o2Map_apply, blkOf_blkVec, blkOf_blkVec] at h0
  funext k j
  fin_cases k
  · exact congrFun (congrFun h0 0) j
  · exact congrFun (congrFun h0 1) j

theorem dot_wOne (u : Fin 2 → K) : u ⬝ᵥ wMat 1 c *ᵥ u = u 0 ^ 2 + c * u 1 ^ 2 := by
  simp [wMat, mulVec, dotProduct, Fin.sum_univ_two, diagonal]
  ring

theorem orth2_ts [Fact (Irreducible (sqPoly c))] (hc0 : c ≠ 0) {w : Fin 4 → EAlg c}
    (hw1 : ∀ i : Fin 4, (i : ℕ) + 1 < 4 → w i = 1)
    {l : EAlg c} (hl : l ≠ 0) (hlw : l ^ 2 = w 3) {α β : K} (hαβ : α ^ 2 + β ^ 2 = -1)
    {R : GL (Fin (2 * 4)) K}
    (hR : (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) =
      blkDiag 4 (wMat 1 c) * resMat (phiE c).toRingHom 4 (diagonal w)) :
    IsTS (oQ R) 4 (LinearMap.range (o2Map (phiE c l⁻¹) α β)) := by
  have hRb : (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) =
      blkDiagF fun i => wMat 1 c * phiE c (w i) := by
    rw [hR, blkDiag_eq, resMat_diagonal_eq, blkDiagF_mul]
    rfl
  refine ⟨?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj (o2Map_injective _ α β)]
    simp [Module.finrank_pi_fintype]
  · rintro _ ⟨x, rfl⟩
    rw [o2Map_apply, oQ_apply, hRb, dot_blkDiagF, Fin.sum_univ_four]
    have h0 : w 0 = 1 := hw1 0 (by decide)
    have h1 : w 1 = 1 := hw1 1 (by decide)
    have h2 : w 2 = 1 := hw1 2 (by decide)
    rw [h0, h1, h2, map_one, Matrix.mul_one]
    have h3 : ∀ y : Fin 2 → K, (phiE c l⁻¹ *ᵥ y) ⬝ᵥ (wMat 1 c * phiE c (w 3)) *ᵥ
        (phiE c l⁻¹ *ᵥ y) = y ⬝ᵥ wMat 1 c *ᵥ y := by
      intro y
      rw [← dotProduct_transpose_mul_mul, ← Matrix.mul_assoc, transpose_phiE_mul_wOne hc0,
        Matrix.mul_assoc, Matrix.mul_assoc, ← map_mul, ← map_mul, ← hlw,
        show l⁻¹ * (l ^ 2 * l⁻¹) = 1 by field_simp, map_one, Matrix.mul_one]
    change x 0 ⬝ᵥ wMat 1 c *ᵥ x 0 + x 1 ⬝ᵥ wMat 1 c *ᵥ x 1 +
      (α • x 0 + β • x 1) ⬝ᵥ wMat 1 c *ᵥ (α • x 0 + β • x 1) +
      (phiE c l⁻¹ *ᵥ (-β • x 0 + α • x 1)) ⬝ᵥ (wMat 1 c * phiE c (w 3)) *ᵥ
        (phiE c l⁻¹ *ᵥ (-β • x 0 + α • x 1)) = 0
    rw [h3, dot_wOne, dot_wOne, dot_wOne, dot_wOne]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (x 0 0 ^ 2 + c * x 0 1 ^ 2 + x 1 0 ^ 2 + c * x 1 1 ^ 2) * hαβ

theorem o2Map_jMat (l : EAlg c) (α β : K) (x : Fin 2 → Fin 2 → K) :
    blkDiag 4 (jMat c) *ᵥ o2Map (phiE c l) α β x =
      o2Map (phiE c l) α β fun k => jMat c *ᵥ x k := by
  rw [o2Map_apply, o2Map_apply, blkDiag_eq, blkDiagF_mulVec]
  congr 1
  funext i
  fin_cases i
  · rfl
  · rfl
  · change jMat c *ᵥ (α • x 0 + β • x 1) = α • (jMat c *ᵥ x 0) + β • (jMat c *ᵥ x 1)
    rw [mulVec_add, mulVec_smul, mulVec_smul]
  · change jMat c *ᵥ (phiE c l *ᵥ (-β • x 0 + α • x 1)) =
      phiE c l *ᵥ (-β • (jMat c *ᵥ x 0) + α • (jMat c *ᵥ x 1))
    rw [mulVec_mulVec, ← phiE_commute, ← mulVec_mulVec, mulVec_add, mulVec_smul, mulVec_smul]

end TS

theorem orth2_false [Finite K] (hK : ringChar K ≠ 2) {c : K} (hc : ¬ IsSquare c)
    [Fact (Irreducible (sqPoly c))] {w : Fin 4 → EAlg c} (hw : ∀ i, w i ≠ 0)
    (hw1 : ∀ i : Fin 4, (i : ℕ) + 1 < 4 → w i = 1) {R : GL (Fin (2 * 4)) K}
    (hR : (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) =
      blkDiag 4 (wMat 1 c) * resMat (phiE c).toRingHom 4 (diagonal w))
    (hdet : IsSquare (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K).det)
    {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1)
    (hgA : (g.val.left : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = blkDiag 4 (jMat c))
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))}
    {y : MulAut (StatedProj (matrixDerived (oQ R)))} (h : Sit (oQ R) B (oκ _ g) y) : False := by
  have hc0 : c ≠ 0 := fun h0 => hc ⟨0, by rw [h0, mul_zero]⟩
  have hdetR : (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K).det = c ^ 4 * (phiE c (w 3)).det := by
    rw [hR, blkDiag_eq, resMat_diagonal_eq, blkDiagF_mul, det_blkDiagF, Fin.prod_univ_four]
    have hw' : ∀ i : Fin 4, (i : ℕ) + 1 < 4 → (wMat 1 c * (phiE c).toRingHom (w i)).det = c := by
      intro i hi
      rw [hw1 i hi, map_one, Matrix.mul_one, wMat, det_diagonal, Fin.prod_univ_two]
      simp
    rw [hw' 0 (by decide), hw' 1 (by decide), hw' 2 (by decide), det_mul, wMat, det_diagonal,
      Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]
    change c * c * c * (c * (phiE c (w 3)).det) = _
    ring
  have hN : IsSquare (phiE c (w 3)).det := by
    obtain ⟨r, hr⟩ := hdet
    refine ⟨r / c ^ 2, ?_⟩
    have hc4 : c ^ 4 ≠ 0 := pow_ne_zero 4 hc0
    rw [hdetR] at hr
    field_simp
    linear_combination hr
  obtain ⟨l, hl⟩ := isSquare_of_isSquare_det_phiE hK hc (hw 3) hN
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact hw 3 (by rw [hl, mul_zero])
  obtain ⟨α, β, hαβ⟩ := exists_sq_sub_mul_sq hK (neg_ne_zero.2 one_ne_zero) (-1)
  have hαβ' : α ^ 2 + β ^ 2 = -1 := by linear_combination hαβ
  have hW := orth2_ts hc0 hw1 hl0 (by rw [hl, sq]) hαβ' hR
  have hA2 : (g.val.left : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) * g.val.left = c • 1 := by
    rw [hgA, blkDiag_eq, blkDiagF_mul, jMat_mul_self, ← blkDiag_eq (c • 1), blkDiag_smul,
      blkDiag_one']
  refine tri_false_of_ts h hg1 rfl hW ?_ (fun v hv l => no_eigen_of_sq hA2 hc hv l)
  have hle : subPerm g.val.left (LinearMap.range (o2Map (phiE c l⁻¹) α β)) ≤
      LinearMap.range (o2Map (phiE c l⁻¹) α β) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    change (g.val.left : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ o2Map (phiE c l⁻¹) α β x ∈ _
    rw [hgA, o2Map_jMat]
    exact ⟨_, rfl⟩
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [subPerm_apply, LinearEquiv.finrank_map_eq]

end CFSG.ComponentClassification.Burgoyne.D4
