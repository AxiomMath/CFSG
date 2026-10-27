module

public import CFSG.ClassicalInvolution.Phan.PhanS10Vec

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H

section Fix

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K)

theorem two_smul_emb_e :
    (2 : K) • emb (K := K) (mk7 0 1 0 0 1 0 0 : W7 F) = vE3 D + conjV D (vE3 D) := by
  rw [conjV_vE3, vE3]
  funext t
  rcases t with i | i | u
  · fin_cases i <;> simp [emb, mk7, one_add_one_eq_two]
  · fin_cases i <;> simp [emb, mk7, one_add_one_eq_two]
  · simp [emb, mk7]

theorem two_theta_smul_emb_f :
    (2 * D.θ) • emb (K := K) (mk7 0 0 1 0 0 1 0 : W7 F) = vE3 D - conjV D (vE3 D) := by
  rw [conjV_vE3, vE3]
  funext t
  rcases t with i | i | u
  · fin_cases i <;> simp [emb, mk7, two_mul]
  · fin_cases i <;> simp [emb, mk7, two_mul]
  · simp [emb, mk7]

theorem fix_Ppp_of_fix_vE3 (h2 : (2 : K) ≠ 0) {g : spinGroup (quadOdd 3 F)}
    (h : actK g (vE3 D) = vE3 D) :
    spinAction (quadOdd 3 F) g (mk7 0 1 0 0 1 0 0) = mk7 0 1 0 0 1 0 0 ∧
      spinAction (quadOdd 3 F) g (mk7 0 0 1 0 0 1 0) = mk7 0 0 1 0 0 1 0 := by
  have hc : actK g (conjV D (vE3 D)) = conjV D (vE3 D) := by rw [actK_conjV, h]
  have h2θ : (2 * D.θ : K) ≠ 0 := mul_ne_zero h2 (theta_ne_zero D)
  constructor
  · apply emb_injective (K := K)
    rw [← actK_emb]
    have key : (2 : K) • actK g (emb (K := K) (mk7 0 1 0 0 1 0 0 : W7 F)) =
        (2 : K) • emb (K := K) (mk7 0 1 0 0 1 0 0 : W7 F) := by
      rw [← map_smul, two_smul_emb_e, map_add, h, hc]
    exact smul_right_injective (W7 K) h2 key
  · apply emb_injective (K := K)
    rw [← actK_emb]
    have key : (2 * D.θ) • actK g (emb (K := K) (mk7 0 0 1 0 0 1 0 : W7 F)) =
        (2 * D.θ) • emb (K := K) (mk7 0 0 1 0 0 1 0 : W7 F) := by
      rw [← map_smul, two_theta_smul_emb_f, map_sub, h, hc]
    exact smul_right_injective (W7 K) h2θ key

theorem fix_six_of_fix_frame (h2 : (2 : K) ≠ 0) {g : spinGroup (quadOdd 3 F)}
    (h₁ : actK g (vXi D) = vXi D) (h₂ : actK g (vE2 D) = vE2 D) (h₃ : actK g (vE3 D) = vE3 D) :
    spinAction (quadOdd 3 F) g (mk7 1 0 0 1 0 0 0) = mk7 1 0 0 1 0 0 0 ∧
      spinAction (quadOdd 3 F) g (mk7 0 0 0 0 0 0 1) = mk7 0 0 0 0 0 0 1 ∧
      spinAction (quadOdd 3 F) g (mk7 0 1 0 0 (-1) 0 0) = mk7 0 1 0 0 (-1) 0 0 ∧
      spinAction (quadOdd 3 F) g (mk7 0 0 1 0 0 (-1) 0) = mk7 0 0 1 0 0 (-1) 0 ∧
      spinAction (quadOdd 3 F) g (mk7 0 1 0 0 1 0 0) = mk7 0 1 0 0 1 0 0 ∧
      spinAction (quadOdd 3 F) g (mk7 0 0 1 0 0 1 0) = mk7 0 0 1 0 0 1 0 := by
  obtain ⟨a1, a2⟩ := fix_P_of_fix_vXi D h2 h₁
  obtain ⟨a3, a4⟩ := fix_Pp_of_fix_vE2 D h2 h₂
  obtain ⟨a5, a6⟩ := fix_Ppp_of_fix_vE3 D h2 h₃
  exact ⟨a1, a2, a3, a4, a5, a6⟩

end Fix

section Decomp

variable {F : Type} [Field F]

theorem mk7_decomp7 (h2 : (2 : F) ≠ 0) (x0 x1 x2 y0 y1 y2 z : F) :
    mk7 x0 x1 x2 y0 y1 y2 z =
      ((x0 + y0) / 2) • (mk7 1 0 0 1 0 0 0 : W7 F) + z • (mk7 0 0 0 0 0 0 1 : W7 F) +
      ((x1 - y1) / 2) • (mk7 0 1 0 0 (-1) 0 0 : W7 F) +
      ((x2 - y2) / 2) • (mk7 0 0 1 0 0 (-1) 0 : W7 F) +
      ((x1 + y1) / 2) • (mk7 0 1 0 0 1 0 0 : W7 F) +
      ((x2 + y2) / 2) • (mk7 0 0 1 0 0 1 0 : W7 F) +
      ((x0 - y0) / 2) • (mk7 1 0 0 (-1) 0 0 0 : W7 F) := by
  funext t
  rcases t with i | i | u
  · fin_cases i <;> simp [mk7] <;> field_simp <;> ring
  · fin_cases i <;> simp [mk7] <;> field_simp <;> ring
  · simp [mk7]

end Decomp

end CFSG.ClassicalInvolution.PhanB3.S
