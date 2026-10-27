module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.SplitBLetters

public section

namespace CFSG.EvenSporadicStandard.M24Std.SplitB

open Matrix

theorem exists_tvPair : ∀ i j : Fin 4, i ≠ j → ∃ k : Fin 12, tvPair k = (i, j) := by
  decide

theorem exists_word_transvection (t : TransvectionStruct (Fin 4) F2) :
    ∃ l : List (Fin 12), wordMat Atv l = t.toMatrix := by
  rcases F2_cases t.c with hc | hc
  · exact ⟨[], by simp [wordMat, TransvectionStruct.toMatrix, hc]⟩
  · obtain ⟨k, hk⟩ := exists_tvPair t.i t.j t.hij
    refine ⟨[k], ?_⟩
    simp only [wordMat, Matrix.one_mul, Atv, hk, TransvectionStruct.toMatrix, hc]

theorem exists_word_prod (L : List (TransvectionStruct (Fin 4) F2)) :
    ∃ l : List (Fin 12), wordMat Atv l = (L.map TransvectionStruct.toMatrix).prod := by
  induction L with
  | nil => exact ⟨[], rfl⟩
  | cons t L ih =>
    obtain ⟨l, hl⟩ := ih
    obtain ⟨l₁, hl₁⟩ := exists_word_transvection t
    refine ⟨l ++ l₁, ?_⟩
    rw [wordMat_append, hl₁, hl, List.map_cons, List.prod_cons]

theorem exists_word_of_mul_eq_one (M N : Mat4) (h : M * N = 1) :
    ∃ l : List (Fin 12), wordMat Atv l = M := by
  obtain ⟨L, L', D, hM⟩ := Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M
  have hdet : M.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  have hD : diagonal D = 1 := by
    have hd : (diagonal D).det ≠ 0 := by
      rw [hM] at hdet
      simpa [det_mul, TransvectionStruct.det_toMatrix_prod] using hdet
    rw [det_diagonal] at hd
    ext i j
    have hi : D i ≠ 0 := fun h0 => hd (Finset.prod_eq_zero (Finset.mem_univ i) h0)
    have hi1 : D i = 1 := (F2_cases (D i)).resolve_left hi
    by_cases hij : i = j
    · subst hij
      simp [hi1]
    · simp [diagonal_apply_ne _ hij, one_apply_ne hij]
  obtain ⟨l, hl⟩ := exists_word_prod L
  obtain ⟨l', hl'⟩ := exists_word_prod L'
  refine ⟨l' ++ l, ?_⟩
  rw [wordMat_append, hl, hl', hM, hD, Matrix.mul_one]

end CFSG.EvenSporadicStandard.M24Std.SplitB
