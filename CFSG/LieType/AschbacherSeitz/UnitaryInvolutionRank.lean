module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.LinearAlgebra.LinearGroups.UnitaryFourOrder

public section

namespace CFSG.LieType.AschbacherSeitz

open Matrix Module CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LinearGroups CFSG.Open

variable {p f : ℕ} {K : Type} [Field K]

theorem finrank_le_two_of_totallyIsotropic (h : UnitaryFieldData p f K) (p2 : p = 2)
    (U : Submodule K (Fin 4 → K))
    (hU : ∀ x ∈ U, ∀ y ∈ U, stdHermForm h 4 x y = 0) :
    Module.finrank K U ≤ 2 := by
  classical
  by_contra hle
  push Not at hle
  obtain ⟨u, hu⟩ := exists_linearIndependent_of_le_finrank (R := K) (M := U) hle
  let uV : Fin 3 → (Fin 4 → K) := fun i => (u i : Fin 4 → K)
  have huV : LinearIndependent K uV :=
    hu.map' (Submodule.subtype U) (Submodule.ker_subtype U)
  have hspan_lt : Submodule.span K (Set.range uV) < ⊤ := by
    refine Submodule.lt_top_of_finrank_lt_finrank ?_
    rw [finrank_span_eq_card huV, Fintype.card_fin, Module.finrank_fin_fun]
    norm_num
  obtain ⟨w, hw⟩ : ∃ w : Fin 4 → K, w ∉ Submodule.span K (Set.range uV) := by
    by_contra h
    push Not at h
    exact hspan_lt.ne (Submodule.eq_top_iff'.2 h)
  let b : Fin 4 → (Fin 4 → K) := Fin.snoc uV w
  have hb : LinearIndependent K b := by
    simpa [b] using huV.finSnoc hw
  have hspan_top : Submodule.span K (Set.range b) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [finrank_span_eq_card hb, Fintype.card_fin, Module.finrank_fin_fun]
  let B : Basis (Fin 4) K (Fin 4 → K) := Basis.mk hb (by rw [hspan_top])
  let P : Matrix (Fin 4) (Fin 4) K := (Pi.basisFun K (Fin 4)).toMatrix B
  have hPdet : P.det ≠ 0 := by
    apply Matrix.det_ne_zero_of_right_inverse
    dsimp only [P]
    exact Basis.toMatrix_mul_toMatrix_flip (b := Pi.basisFun K (Fin 4)) (b' := B)
  let G : Matrix (Fin 4) (Fin 4) K := (P.map h.bar)ᵀ * P
  have hG_eq : ∀ i j : Fin 4, G i j = stdHermForm h 4 (B i) (B j) := by
    intro i j
    dsimp only [G, P]
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, Matrix.map_apply, Basis.toMatrix_apply,
      Pi.basisFun_repr, stdHermForm_apply]
  have hGdet : G.det ≠ 0 := by
    have hbarPdet : h.bar P.det ≠ 0 := by
      intro h0
      exact hPdet ((RingHom.injective h.bar) (by rw [h0, map_zero]))
    have hmapdet : (P.map h.bar).det = h.bar P.det := by
      simpa using (RingHom.map_det h.bar P).symm
    have hdet : G.det = h.bar P.det * P.det := by
      dsimp only [G]
      rw [Matrix.det_mul, Matrix.det_transpose, hmapdet]
    rw [hdet]
    exact mul_ne_zero hbarPdet hPdet
  have hGrank : G.rank = 4 := by
    rw [Matrix.rank_of_det_ne_zero hGdet]
    simp
  have hG_iso : ∀ i j : Fin 3, G (Fin.castSucc i) (Fin.castSucc j) = 0 := by
    intro i j
    rw [hG_eq]
    have hi : B (Fin.castSucc i) = (u i : Fin 4 → K) := by
      simp [B, b, uV, Fin.snoc_castSucc]
    have hj : B (Fin.castSucc j) = (u j : Fin 4 → K) := by
      simp [B, b, uV, Fin.snoc_castSucc]
    rw [hi, hj]
    exact hU (u i) (u i).2 (u j) (u j).2
  have hG_iso4 : ∀ i j : Fin 4, i.val < 3 → j.val < 3 → G i j = 0 := by
    intro i j hi hj
    have hi' : i = Fin.castSucc ⟨i.val, hi⟩ := Fin.ext rfl
    have hj' : j = Fin.castSucc ⟨j.val, hj⟩ := Fin.ext rfl
    rw [hi', hj']
    exact hG_iso ⟨i.val, hi⟩ ⟨j.val, hj⟩
  have h00 : G 0 0 = 0 := hG_iso4 0 0 (by norm_num) (by norm_num)
  have h01 : G 0 1 = 0 := hG_iso4 0 1 (by norm_num) (by norm_num)
  have h02 : G 0 2 = 0 := hG_iso4 0 2 (by norm_num) (by norm_num)
  have h10 : G 1 0 = 0 := hG_iso4 1 0 (by norm_num) (by norm_num)
  have h11 : G 1 1 = 0 := hG_iso4 1 1 (by norm_num) (by norm_num)
  have h12 : G 1 2 = 0 := hG_iso4 1 2 (by norm_num) (by norm_num)
  have h20 : G 2 0 = 0 := hG_iso4 2 0 (by norm_num) (by norm_num)
  have h21 : G 2 1 = 0 := hG_iso4 2 1 (by norm_num) (by norm_num)
  have h22 : G 2 2 = 0 := hG_iso4 2 2 (by norm_num) (by norm_num)
  let A₂ : Matrix (Fin 4) (Fin 2) K := fun i k =>
    if k = 0 then (if i = 3 then 1 else 0) else G i 3
  let B₂ : Matrix (Fin 2) (Fin 4) K := fun k j =>
    if k = 0 then (if j = 3 then 0 else G 3 j) else (if j = 3 then 1 else 0)
  have hdecomp : G = A₂ * B₂ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      rw [Matrix.mul_apply, Fin.sum_univ_two] <;>
      simp [A₂, B₂, h00, h01, h02, h10, h11, h12, h20, h21, h22]
  have hrank_le : G.rank ≤ 2 := by
    rw [hdecomp]
    refine (Matrix.rank_mul_le_left A₂ B₂).trans ?_
    simpa using Matrix.rank_le_card_width A₂
  omega

end CFSG.LieType.AschbacherSeitz

end
