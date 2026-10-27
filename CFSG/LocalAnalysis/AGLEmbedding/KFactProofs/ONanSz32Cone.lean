module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSz32Data

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sz32

open CFSG.Blueprint Matrix

theorem onOmega4_smul {a : ℕ} {K : Type} [Field K] {l : K} (hl : l ≠ 0) (y0 y1 y2 y3 : K) :
    OnOmega4 a (l * y0) (l * y1) (l * y2) (l * y3) ↔ OnOmega4 a y0 y1 y2 y3 := by
  unfold OnOmega4
  have hp : l ^ (2 ^ (a + 1) + 2) ≠ 0 := pow_ne_zero _ hl
  have e : (l * y3) * (l * y0) ^ (2 ^ (a + 1) + 1) =
      l ^ (2 ^ (a + 1) + 2) * (y3 * y0 ^ (2 ^ (a + 1) + 1)) := by ring
  have e' : (l * y1) ^ (2 ^ (a + 1) + 2) + (l * y1) * (l * y2) * (l * y0) ^ 2 ^ (a + 1) +
      (l * y2) ^ 2 ^ (a + 1) * (l * y0) ^ 2 = l ^ (2 ^ (a + 1) + 2) *
        (y1 ^ (2 ^ (a + 1) + 2) + y1 * y2 * y0 ^ 2 ^ (a + 1) + y2 ^ 2 ^ (a + 1) * y0 ^ 2) := by
    ring
  rw [e, e', mul_right_inj' hp]
  simp only [mul_eq_zero, hl, false_or, ne_eq]

theorem onOmegaGen_smul {l : F32} (hl : l ≠ 0) (y : Vec) :
    OnOmegaGen 2 (l • y) ↔ OnOmegaGen 2 y :=
  onOmega4_smul hl _ _ _ _

theorem exists_cone {w : Vec} (hw : OnOmegaGen 2 w) :
    (∃ l : F32, l ≠ 0 ∧ ∃ u v : F32, w = l • lineVec u v) ∨
      (∃ l : F32, l ≠ 0 ∧ w = l • inftyVec) := by
  rcases hw with ⟨h0, h1, h2, h3⟩ | ⟨h0, heq⟩
  · right
    refine ⟨w 3, h3, funext fun i => ?_⟩
    fin_cases i <;> simp [inftyVec, h0, h1, h2]
  · left
    refine ⟨w 0, h0, w 1 / w 0, w 2 / w 0, funext fun i => ?_⟩
    norm_num at heq
    fin_cases i
    · simp [lineVec]
    · simp [lineVec]
      field_simp
    · simp [lineVec]
      field_simp
    · simp [lineVec, suzukiN]
      field_simp
      linear_combination heq

theorem e0_eq_lineVec : e0 = lineVec 0 0 := by
  funext i
  fin_cases i <;> simp [e0, lineVec, suzukiN]

theorem polyMat_smul (l c0 c1 c2 c3 : F32) :
    polyMat (l * c0) (l * c1) (l * c2) (l * c3) = l • polyMat c0 c1 c2 c3 := by
  rw [polyMat_eq, polyMat_eq]
  simp only [smul_add, smul_smul]

theorem pow_four_eq_one : ∀ x : F32, x ^ 4 = 1 → x = 1 := by decide +kernel

theorem pow_25_eq_one : ∀ x : F32, x ^ 25 = 1 → x = 1 := by decide +kernel

theorem det_g0Mat : g0Mat.det = 1 :=
  pow_25_eq_one _ (by rw [← Matrix.det_pow, g0Mat_pow_25, Matrix.det_one])

end CFSG.AGLEmbedding.KFactProofs.Sz32
