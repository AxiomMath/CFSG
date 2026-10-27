module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommUniModel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.Uni

open Matrix Module CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.AGLEmbedding.LeviBlock
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Uni
open scoped Pointwise

section Pow

variable {K : Type} [Field K] {r ε : ℕ}

theorem cutPat_pow {c : ℕ} {N : Matrix (HypIndex r ε) (HypIndex r ε) K} (hN : CutPat c N)
    (m : ℕ) : CutPat c (N ^ m) := by
  induction m with
  | zero =>
    rw [pow_zero]
    exact CutPat.one c
  | succ m ih =>
    rw [pow_succ]
    exact ih.mul hN

theorem submatrix_pow_of_cutPat {ι : Type} [Fintype ι] [DecidableEq ι] {φ : ι → HypIndex r ε}
    (hφ : Function.Injective φ) {a b : ℕ}
    (hrange : ∀ x, x ∈ Set.range φ ↔ a ≤ fullPos x ∧ fullPos x < b)
    {N : Matrix (HypIndex r ε) (HypIndex r ε) K} (hNa : CutPat a N) (hNb : CutPat b N)
    (m : ℕ) : (N ^ m).submatrix φ φ = (N.submatrix φ φ) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, Matrix.submatrix_one _ hφ]
  | succ m ih =>
    rw [pow_succ, pow_succ, submatrix_mul_of_cutPat hφ hrange (cutPat_pow hNa m) hNb, ih]

theorem submatrix_conj_mul_eq_one {ι : Type} [Fintype ι] [DecidableEq ι] {φ : ι → HypIndex r ε}
    (hφ : Function.Injective φ) {a b : ℕ}
    (hrange : ∀ x, x ∈ Set.range φ ↔ a ≤ fullPos x ∧ fullPos x < b)
    {M M' X Y : Matrix (HypIndex r ε) (HypIndex r ε) K} (hMa : CutPat a M) (hMb : CutPat b M)
    (hM'a : CutPat a M') (hM'b : CutPat b M') (hXa : CutPat a X) (hXb : CutPat b X)
    (hYb : CutPat b Y) (e : M * M' = 1) {c : K} (hX : X.submatrix φ φ = c • 1)
    (hY : c • Y.submatrix φ φ = 1) : (M * X * M' * Y).submatrix φ φ = 1 := by
  have mb : ∀ {A B : Matrix (HypIndex r ε) (HypIndex r ε) K}, CutPat a A → CutPat b B →
      (A * B).submatrix φ φ = A.submatrix φ φ * B.submatrix φ φ :=
    fun hA hB => submatrix_mul_of_cutPat hφ hrange hA hB
  have i₁ : M.submatrix φ φ * M'.submatrix φ φ = 1 := by
    rw [← mb hMa hM'b, e, Matrix.submatrix_one _ hφ]
  rw [mb ((hMa.mul hXa).mul hM'a) hYb, mb (hMa.mul hXa) hM'b, mb hMa hXb, hX,
    Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, i₁, Matrix.smul_mul, Matrix.one_mul, hY]

end Pow

section Sim

variable {f : ℕ} {K : Type} [Field K] {ε : ℕ} {h : UnitaryFieldData 2 f K}

theorem sim_pow {r : ℕ} {A : Matrix (HypIndex r ε) (HypIndex r ε) K} {a : K}
    (hA : (A.map h.bar)ᵀ * hypGram r ε K * A = a • hypGram r ε K) (m : ℕ) :
    ((A ^ m).map h.bar)ᵀ * hypGram r ε K * A ^ m = a ^ m • hypGram r ε K := by
  induction m with
  | zero =>
    simp only [pow_zero, Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one,
      Matrix.one_mul, Matrix.mul_one, one_smul]
  | succ m ih =>
    rw [pow_succ, pow_succ]
    exact sim_mul ih hA

end Sim

section Unipotent

variable {f : ℕ} {K : Type} [Field K] {t s ε : ℕ} {h : UnitaryFieldData 2 f K} {I : Finset ℕ}

theorem exists_pow_two_eq_one_of_blocks (hε : ε ≤ 1) (hI : IsTopCut I t)
    {C : GL (HypIndex (t + s) ε) K}
    (hsim : ((C : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K).map h.bar)ᵀ *
      hypGram (t + s) ε K * C = hypGram (t + s) ε K)
    (hdet : (C : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K).det = 1)
    (hf : ∀ c ∈ I, C • hypFlag h (t + s) ε c = hypFlag h (t + s) ε c)
    (hb : ∀ b : ↥I, blkE hI b (C : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) = 1)
    (hr : blkRes t (C : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) = 1) :
    ∃ k : ℕ, C ^ 2 ^ k = 1 := by
  have hCS : C ∈ hypSU h (t + s) ε := mem_hypSU.mpr ⟨hsim, hdet⟩
  let x : ↥(flagStabilizer h (t + s) ε ↑I) :=
    ⟨⟨C, hCS⟩, mem_flagStabilizer.mpr fun c hc => hf c hc⟩
  have hker : x ∈ (uniLeviHom (s := s) h hε hI).ker := by
    rw [MonoidHom.mem_ker]
    funext j
    rcases j with _ | b
    · show resBlockHom h hε (Finset.mem_coe.mpr hI.mem) x = 1
      refine Units.ext ?_
      rw [coe_resBlockHom, Units.val_one]
      exact hr
    · have hbr : b.1 ≤ t + s := (hI.le b.1 b.2).2.trans (Nat.le_add_right t s)
      have hb1 : 1 ≤ b.1 := (hI.le b.1 b.2).1
      show eBlockHom h hε b.2 hb1 hbr x = 1
      refine Units.ext ?_
      rw [coe_eBlockHom, Units.val_one]
      exact hb b
  obtain ⟨k, hk⟩ := isPGroup_ker_uniLeviHom (s := s) h hε hI ⟨x, hker⟩
  refine ⟨k, ?_⟩
  have h1 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h2 := congrArg (fun y : ↥(flagStabilizer h (t + s) ε ↑I) =>
    ((y : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K)) h1
  have hxC : ((x : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K) = C := rfl
  simpa [hxC] using h2

end Unipotent

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.Uni
