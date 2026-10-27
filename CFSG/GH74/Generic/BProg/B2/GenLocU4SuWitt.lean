module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4SuBase

public section

namespace CFSG.GH74.Generic.BProg.B2.GenLocU4Su

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups
open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4 (aSU suMat_aSU suMat_blockEmb_zero
  suMat_blockEmb_two suMat_rootInvSU_four)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_witt_pair (h2 : (2 : K) ≠ 0) {ι : K} (hι : ι * ι = -1)
    (hσι : unitaryInvolution K p f ι = ι) (B : Su K p f 2) (hB : suMat B * suMat B = -1) :
    ∃ fp fm : Fin 2 → K, suMat B *ᵥ fp = ι • fp ∧ suMat B *ᵥ fm = (-ι) • fm ∧
      unitaryInvolution K p f (fp 0) * fp 0 + unitaryInvolution K p f (fp 1) * fp 1 = 0 ∧
      unitaryInvolution K p f (fm 0) * fm 0 + unitaryInvolution K p f (fm 1) * fm 1 = 0 ∧
      unitaryInvolution K p f (fp 0) * fm 0 + unitaryInvolution K p f (fp 1) * fm 1 = 1 := by
  set σ := unitaryInvolution K p f with hσdef
  set Bm := suMat B with hBm
  have hB' : conjTr σ Bm = -Bm := conjTr_eq_neg_of_sq B hB
  have hdet : Bm.det = 1 := B.2.1
  set Xp : Matrix (Fin 2) (Fin 2) K := Bm + ι • 1 with hXp
  set Xm : Matrix (Fin 2) (Fin 2) K := Bm - ι • 1 with hXm
  set Y : Matrix (Fin 2) (Fin 2) K := 1 + ι • Bm with hY
  have hBe : ∀ i j, σ (Bm j i) = -Bm i j := by
    intro i j
    have := congrFun (congrFun hB' i) j
    simpa [conjTr] using this
  have hone : ∀ i j, σ ((1 : Matrix (Fin 2) (Fin 2) K) j i) =
      (1 : Matrix (Fin 2) (Fin 2) K) i j := by
    intro i j
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]
  have hcXp : conjTr σ Xp = -Bm + ι • 1 := by
    ext a b
    simp only [hXp, conjTr, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply,
      Matrix.smul_apply, Matrix.neg_apply, map_add, map_mul, hσι, smul_eq_mul, hBe, hone]
  have hcXm : conjTr σ Xm = -Bm - ι • 1 := by
    ext a b
    simp only [hXm, conjTr, Matrix.transpose_apply, Matrix.map_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.neg_apply, map_sub, map_mul, hσι, smul_eq_mul, hBe, hone]
  have P1 : conjTr σ Xp * Xp = 0 := by
    rw [hcXp, hXp]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, hB]
    match_scalars <;> first | ring1 | linear_combination hι
  have P2 : conjTr σ Xm * Xm = 0 := by
    rw [hcXm, hXm]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, hB]
    match_scalars <;> first | ring1 | linear_combination hι
  have P3 : conjTr σ Xp * Xm = (2 : K) • Y := by
    rw [hcXp, hXm, hY]
    simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.neg_mul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hB]
    match_scalars <;> first | ring1 | linear_combination hι | linear_combination (-1 : K) * hι
  have P4 : Bm * Xp = ι • Xp := by
    rw [hXp]
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, smul_add, smul_smul, hB, hι]
    match_scalars <;> ring1
  have P5 : Bm * Xm = (-ι) • Xm := by
    rw [hXm]
    simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, smul_sub, smul_smul, hB]
    match_scalars <;> first | ring1 | linear_combination hι | linear_combination (-1 : K) * hι
  have hι0 : ι ≠ 0 := by
    rintro rfl
    simp at hι
  have hY0 : Y ≠ 0 := by
    intro h0
    have e00 : 1 + ι * Bm 0 0 = 0 := by
      have := congrFun (congrFun h0 0) 0
      simpa [hY] using this
    have e11 : 1 + ι * Bm 1 1 = 0 := by
      have := congrFun (congrFun h0 1) 1
      simpa [hY] using this
    have e01 : ι * Bm 0 1 = 0 := by
      have := congrFun (congrFun h0 0) 1
      simpa [hY] using this
    have e10 : ι * Bm 1 0 = 0 := by
      have := congrFun (congrFun h0 1) 0
      simpa [hY] using this
    have b01 : Bm 0 1 = 0 := (mul_eq_zero.mp e01).resolve_left hι0
    have b10 : Bm 1 0 = 0 := (mul_eq_zero.mp e10).resolve_left hι0
    have b00 : Bm 0 0 = ι := by linear_combination (-ι) * e00 + (Bm 0 0) * hι
    have b11 : Bm 1 1 = ι := by linear_combination (-ι) * e11 + (Bm 1 1) * hι
    have := hdet
    rw [Matrix.det_fin_two, b00, b11, b01, b10] at this
    apply h2
    linear_combination hι - this
  obtain ⟨i, j, hij⟩ : ∃ i j, Y i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hY0 (by ext a b; exact hcon a b)
  set c : K := (2 * Y i j)⁻¹ with hc
  have h2Y : 2 * Y i j ≠ 0 := mul_ne_zero h2 hij
  have h4 : Bm *ᵥ (fun r => Xp r i) = ι • fun r => Xp r i := by
    ext r
    have := congrFun (congrFun P4 r) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have h5 : Bm *ᵥ (fun r => Xm r j) = (-ι) • fun r => Xm r j := by
    ext r
    have := congrFun (congrFun P5 r) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have g1 : σ (Xp 0 i) * Xp 0 i + σ (Xp 1 i) * Xp 1 i = 0 := by
    have := congrFun (congrFun P1 i) i
    simpa [conjTr, Matrix.mul_apply, Fin.sum_univ_two] using this
  have g2 : σ (Xm 0 j) * Xm 0 j + σ (Xm 1 j) * Xm 1 j = 0 := by
    have := congrFun (congrFun P2 j) j
    simpa [conjTr, Matrix.mul_apply, Fin.sum_univ_two] using this
  have g3 : σ (Xp 0 i) * Xm 0 j + σ (Xp 1 i) * Xm 1 j = 2 * Y i j := by
    have := congrFun (congrFun P3 i) j
    simpa [conjTr, Matrix.mul_apply, Fin.sum_univ_two] using this
  refine ⟨fun r => Xp r i, c • fun r => Xm r j, h4, ?_, g1, ?_, ?_⟩
  · rw [Matrix.mulVec_smul, h5, smul_comm]
  · show σ (c * Xm 0 j) * (c * Xm 0 j) + σ (c * Xm 1 j) * (c * Xm 1 j) = 0
    simp only [map_mul]
    linear_combination (σ c * c) * g2
  · show σ (Xp 0 i) * (c * Xm 0 j) + σ (Xp 1 i) * (c * Xm 1 j) = 1
    have : c * (2 * Y i j) = 1 := by rw [hc]; exact inv_mul_cancel₀ h2Y
    linear_combination c * g3 + this


@[expose] def wittW (fp fm gp gm : Fin 2 → K) : Matrix (Fin 4) (Fin 4) K :=
  !![fp 0, 0, 0, fm 0; fp 1, 0, 0, fm 1; 0, gp 0, gm 0, 0; 0, gp 1, gm 1, 0]

theorem wittW_gram (fp fm gp gm : Fin 2 → K)
    (hσ : IsUnitaryInvolution (unitaryInvolution K p f))
    (h1 : unitaryInvolution K p f (fp 0) * fp 0 + unitaryInvolution K p f (fp 1) * fp 1 = 0)
    (h2 : unitaryInvolution K p f (fm 0) * fm 0 + unitaryInvolution K p f (fm 1) * fm 1 = 0)
    (h3 : unitaryInvolution K p f (fp 0) * fm 0 + unitaryInvolution K p f (fp 1) * fm 1 = 1)
    (k1 : unitaryInvolution K p f (gp 0) * gp 0 + unitaryInvolution K p f (gp 1) * gp 1 = 0)
    (k2 : unitaryInvolution K p f (gm 0) * gm 0 + unitaryInvolution K p f (gm 1) * gm 1 = 0)
    (k3 : unitaryInvolution K p f (gp 0) * gm 0 + unitaryInvolution K p f (gp 1) * gm 1 = 1) :
    conjTr (unitaryInvolution K p f) (wittW fp fm gp gm) * wittW fp fm gp gm = antidiag 4 := by
  set σ := unitaryInvolution K p f with hσdef
  have h3' : σ (fm 0) * fp 0 + σ (fm 1) * fp 1 = 1 := by
    have := congrArg σ h3
    simp only [map_add, map_mul, hσ.invol, map_one] at this
    linear_combination this
  have k3' : σ (gm 0) * gp 0 + σ (gm 1) * gp 1 = 1 := by
    have := congrArg σ k3
    simp only [map_add, map_mul, hσ.invol, map_one] at this
    linear_combination this
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [wittW, conjTr, Matrix.mul_apply, Fin.sum_univ_four, antidiag, Fin.rev, h1, h2, h3, h3',
      k1, k2, k3, k3']

theorem wittW_det_ne_zero (fp fm gp gm : Fin 2 → K)
    (hgram : conjTr (unitaryInvolution K p f) (wittW fp fm gp gm) * wittW fp fm gp gm =
      antidiag 4) : (wittW fp fm gp gm).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det hgram
  rw [Matrix.det_mul, h, mul_zero] at this
  exact det_antidiag_ne_zero 4 this.symm

theorem xU_mul_wittW (fp fm gp gm : Fin 2 → K) :
    suMat (xU K p f) * wittW fp fm gp gm =
      wittW fp fm gp gm * Matrix.diagonal ![-1, 1, 1, -1] := by
  simp only [xU, suMat_rootInvSU_four]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [wittW, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply]

theorem phiU_mul_wittW {ι : K} (B B' : Su K p f 2) (fp fm gp gm : Fin 2 → K)
    (hfp : suMat B *ᵥ fp = ι • fp) (hfm : suMat B *ᵥ fm = (-ι) • fm)
    (hgp : suMat B' *ᵥ gp = ι • gp) (hgm : suMat B' *ᵥ gm = (-ι) • gm) :
    suMat (phiU K p f (B, B')) * wittW fp fm gp gm =
      wittW fp fm gp gm * Matrix.diagonal ![ι, ι, -ι, -ι] := by
  have e1 := fun r => congrFun hfp r
  have e2 := fun r => congrFun hfm r
  have e3 := fun r => congrFun hgp r
  have e4 := fun r => congrFun hgm r
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 e4
  rw [phiU_apply, suMat_mul, suMat_blockEmb_zero, suMat_blockEmb_two]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [wittW, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply]
  all_goals first
    | linear_combination e1 0 | linear_combination e1 1
    | linear_combination e2 0 | linear_combination e2 1
    | linear_combination e3 0 | linear_combination e3 1
    | linear_combination e4 0 | linear_combination e4 1

end CFSG.GH74.Generic.BProg.B2.GenLocU4Su
