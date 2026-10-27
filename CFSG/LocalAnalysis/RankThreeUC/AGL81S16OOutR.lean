module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16ORad

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.Open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin (quadMinus)

namespace OutLin

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem eq_of_add_eq_zero_char_two {x y : F} (h : x + y = 0) : x = y := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination h - y * h2

theorem RadHyp.e_coords {h : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F} (hh : RadHyp b c h) :
    gv h (fV F idx0) (Sum.inl idx0) = gv h (fV F idx0) (Sum.inr (Sum.inr 0)) ^ 2 +
        b * gv h (fV F idx0) (Sum.inr (Sum.inr 0)) * gv h (fV F idx0) (Sum.inr (Sum.inr 1)) +
        c * gv h (fV F idx0) (Sum.inr (Sum.inr 1)) ^ 2 ∧
      gv h (fV F idx1) (Sum.inl idx1) = gv h (fV F idx1) (Sum.inr (Sum.inr 0)) ^ 2 +
        b * gv h (fV F idx1) (Sum.inr (Sum.inr 0)) * gv h (fV F idx1) (Sum.inr (Sum.inr 1)) +
        c * gv h (fV F idx1) (Sum.inr (Sum.inr 1)) ^ 2 ∧
      gv h (fV F idx1) (Sum.inl idx0) = gv h (fV F idx0) (Sum.inl idx1) +
        b * (gv h (fV F idx0) (Sum.inr (Sum.inr 0)) * gv h (fV F idx1) (Sum.inr (Sum.inr 1)) +
          gv h (fV F idx1) (Sum.inr (Sum.inr 0)) * gv h (fV F idx0) (Sum.inr (Sum.inr 1))) ∧
      gv h (nVec F 0) (Sum.inl idx0) = b * gv h (fV F idx0) (Sum.inr (Sum.inr 1)) ∧
      gv h (nVec F 1) (Sum.inl idx0) = b * gv h (fV F idx0) (Sum.inr (Sum.inr 0)) ∧
      gv h (nVec F 0) (Sum.inl idx1) = b * gv h (fV F idx1) (Sum.inr (Sum.inr 1)) ∧
      gv h (nVec F 1) (Sum.inl idx1) = b * gv h (fV F idx1) (Sum.inr (Sum.inr 0)) := by
  have hne01 : idx0 ≠ idx1 := by decide
  have f00 : gv h (fV F idx0) (Sum.inr (Sum.inl idx0)) = 1 := by
    rw [hh.f_coord]; simp [Pi.single_apply]
  have f01 : gv h (fV F idx0) (Sum.inr (Sum.inl idx1)) = 0 := by
    rw [hh.f_coord]; simp [Pi.single_apply, hne01]
  have f10 : gv h (fV F idx1) (Sum.inr (Sum.inl idx0)) = 0 := by
    rw [hh.f_coord]; simp [Pi.single_apply, hne01]
  have f11 : gv h (fV F idx1) (Sum.inr (Sum.inl idx1)) = 1 := by
    rw [hh.f_coord]; simp [Pi.single_apply]
  have m00 : gv h (nVec F 0) (Sum.inr (Sum.inl idx0)) = 0 := by
    rw [hh.f_coord, nVec_inr_inl]
  have m01 : gv h (nVec F 0) (Sum.inr (Sum.inl idx1)) = 0 := by
    rw [hh.f_coord, nVec_inr_inl]
  have m10 : gv h (nVec F 1) (Sum.inr (Sum.inl idx0)) = 0 := by
    rw [hh.f_coord, nVec_inr_inl]
  have m11 : gv h (nVec F 1) (Sum.inr (Sum.inl idx1)) = 0 := by
    rw [hh.f_coord, nVec_inr_inl]
  have n00 : gv h (nVec F 0) (Sum.inr (Sum.inr 0)) = 1 := by
    rw [hh.n_coord_nVec, nVec_00]
  have n01 : gv h (nVec F 0) (Sum.inr (Sum.inr 1)) = 0 := by
    rw [hh.n_coord_nVec, nVec_01]
  have n10 : gv h (nVec F 1) (Sum.inr (Sum.inr 0)) = 0 := by
    rw [hh.n_coord_nVec, nVec_10]
  have n11 : gv h (nVec F 1) (Sum.inr (Sum.inr 1)) = 1 := by
    rw [hh.n_coord_nVec, nVec_11]
  have hQ0 : quadMinus 3 F b c (gv h (fV F idx0)) = 0 := by
    rw [hh.iso]; exact quadMinus_single_inr idx0
  have hQ1 : quadMinus 3 F b c (gv h (fV F idx1)) = 0 := by
    rw [hh.iso]; exact quadMinus_single_inr idx1
  have hP01 : polar (quadMinus 3 F b c) (gv h (fV F idx0)) (gv h (fV F idx1)) = 0 := by
    rw [polar_gv hh.iso, polar_coords]; simp [Pi.single_apply, hne01]
  have hU0V0 : polar (quadMinus 3 F b c) (gv h (nVec F 0)) (gv h (fV F idx0)) = 0 := by
    rw [polar_gv hh.iso, polar_coords]; simp [Pi.single_apply, hne01]
  have hU1V0 : polar (quadMinus 3 F b c) (gv h (nVec F 1)) (gv h (fV F idx0)) = 0 := by
    rw [polar_gv hh.iso, polar_coords]; simp [Pi.single_apply, hne01]
  have hU0V1 : polar (quadMinus 3 F b c) (gv h (nVec F 0)) (gv h (fV F idx1)) = 0 := by
    rw [polar_gv hh.iso, polar_coords]; simp [Pi.single_apply, hne01]
  have hU1V1 : polar (quadMinus 3 F b c) (gv h (nVec F 1)) (gv h (fV F idx1)) = 0 := by
    rw [polar_gv hh.iso, polar_coords]; simp [Pi.single_apply, hne01]
  simp only [Q_coords, f00, f01] at hQ0
  simp only [Q_coords, f10, f11] at hQ1
  simp only [polar_coords, f00, f01, f10, f11] at hP01
  simp only [polar_coords, f00, f01, f10, f11, m00, m01, m10, m11, n00, n01, n10, n11]
    at hU0V0 hU1V0 hU0V1 hU1V1
  refine ⟨eq_of_add_eq_zero_char_two (by linear_combination hQ0),
    eq_of_add_eq_zero_char_two (by linear_combination hQ1),
    eq_of_add_eq_zero_char_two (by linear_combination hP01),
    eq_of_add_eq_zero_char_two (by linear_combination hU0V0),
    eq_of_add_eq_zero_char_two (by linear_combination hU1V0),
    eq_of_add_eq_zero_char_two (by linear_combination hU0V1),
    eq_of_add_eq_zero_char_two (by linear_combination hU1V1)⟩

theorem RadHyp.ext_params {g g' : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F}
    (hg : RadHyp b c g) (hg' : RadHyp b c g')
    (hm : ∀ (i : Fin (3 - 1)) (k : Fin 2),
      gv g (fV F i) (Sum.inr (Sum.inr k)) = gv g' (fV F i) (Sum.inr (Sum.inr k)))
    (hs : gv g (fV F idx0) (Sum.inl idx1) = gv g' (fV F idx0) (Sum.inl idx1)) : g = g' := by
  obtain ⟨A1, A2, A3, A4, A5, A6, A7⟩ := RadHyp.e_coords hg
  obtain ⟨B1, B2, B3, B4, B5, B6, B7⟩ := RadHyp.e_coords hg'
  have hi : ∀ i : Fin (3 - 1), i = idx0 ∨ i = idx1 := by decide
  have hj : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
  have E00 : gv g (fV F idx0) (Sum.inl idx0) = gv g' (fV F idx0) (Sum.inl idx0) := by
    rw [A1, B1, hm idx0 0, hm idx0 1]
  have E11 : gv g (fV F idx1) (Sum.inl idx1) = gv g' (fV F idx1) (Sum.inl idx1) := by
    rw [A2, B2, hm idx1 0, hm idx1 1]
  have E10 : gv g (fV F idx1) (Sum.inl idx0) = gv g' (fV F idx1) (Sum.inl idx0) := by
    rw [A3, B3, hs, hm idx0 0, hm idx0 1, hm idx1 0, hm idx1 1]
  have N00 : gv g (nVec F 0) (Sum.inl idx0) = gv g' (nVec F 0) (Sum.inl idx0) := by
    rw [A4, B4, hm idx0 1]
  have N01 : gv g (nVec F 1) (Sum.inl idx0) = gv g' (nVec F 1) (Sum.inl idx0) := by
    rw [A5, B5, hm idx0 0]
  have N10 : gv g (nVec F 0) (Sum.inl idx1) = gv g' (nVec F 0) (Sum.inl idx1) := by
    rw [A6, B6, hm idx1 1]
  have N11 : gv g (nVec F 1) (Sum.inl idx1) = gv g' (nVec F 1) (Sum.inl idx1) := by
    rw [A7, B7, hm idx1 0]
  have hF : ∀ (i : Fin (3 - 1)) (k : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2),
      gv g (fV F i) k = gv g' (fV F i) k := by
    intro i k
    rcases hi i with rfl | rfl <;> rcases k with k | k | k
    · rcases hi k with rfl | rfl
      · exact E00
      · exact hs
    · rw [hg.f_coord, hg'.f_coord]
    · exact hm _ k
    · rcases hi k with rfl | rfl
      · exact E10
      · exact E11
    · rw [hg.f_coord, hg'.f_coord]
    · exact hm _ k
  have hN : ∀ (j : Fin 2) (k : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2),
      gv g (nVec F j) k = gv g' (nVec F j) k := by
    intro j k
    rcases hj j with rfl | rfl <;> rcases k with k | k | k
    · rcases hi k with rfl | rfl
      · exact N00
      · exact N10
    · rw [hg.f_coord, hg'.f_coord]
    · rw [hg.n_coord_nVec, hg'.n_coord_nVec]
    · rcases hi k with rfl | rfl
      · exact N01
      · exact N11
    · rw [hg.f_coord, hg'.f_coord]
    · rw [hg.n_coord_nVec, hg'.n_coord_nVec]
  apply gl_ext
  intro x
  funext k
  rw [gv_apply_decomp g x k, gv_apply_decomp g' x k, hg.fixE idx0, hg'.fixE idx0, hg.fixE idx1,
    hg'.fixE idx1, hF idx0 k, hF idx1 k, hN 0 k, hN 1 k]

end OutLin

end CFSG.LocalAnalysis.RankThreeUC
