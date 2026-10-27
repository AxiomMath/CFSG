module

public import CFSG.ClassicalInvolution.Phan.PhanH6Fix
public import CFSG.ClassicalInvolution.Phan.PhanS7Ctx

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

section Hrm

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K)

theorem conjV_mk7 (a b c d e f g : K) :
    conjV D (mk7 a b c d e f g) =
      mk7 (D.τ a) (D.τ b) (D.τ c) (D.τ d) (D.τ e) (D.τ f) (D.τ g) := by
  funext s
  rcases s with i | i | u
  · fin_cases i <;> simp [conjV_apply, mk7]
  · fin_cases i <;> simp [conjV_apply, mk7]
  · simp [conjV_apply, mk7]

theorem conjV_vXi : conjV D (vXi D) = mk7 1 0 0 1 0 0 (-D.θ) := by
  rw [vXi, conjV_mk7]
  simp [D.tau_theta]

theorem conjV_vE2 : conjV D (vE2 D) = mk7 0 1 D.θ 0 (-1) (-D.θ) 0 := by
  rw [vE2, conjV_mk7]
  simp [D.tau_theta]

theorem conjV_vE3 : conjV D (vE3 D) = mk7 0 1 (-D.θ) 0 1 (-D.θ) 0 := by
  rw [vE3, conjV_mk7]
  simp [D.tau_theta]

theorem hrm_vXi_vXi : hrm D (vXi D) (vXi D) = 4 := by
  rw [hrm, conjV_vXi, vXi, polar_mk7]
  linear_combination (-2 : K) * D.theta_sq

theorem hrm_vE2_vE2 : hrm D (vE2 D) (vE2 D) = -4 := by
  rw [hrm, conjV_vE2, vE2, polar_mk7]
  linear_combination (2 : K) * D.theta_sq

theorem hrm_vE3_vE3 : hrm D (vE3 D) (vE3 D) = 4 := by
  rw [hrm, conjV_vE3, vE3, polar_mk7]
  linear_combination (-2 : K) * D.theta_sq

theorem hrm_vXi_vE2 : hrm D (vXi D) (vE2 D) = 0 := by
  rw [hrm, conjV_vE2, vXi, polar_mk7]
  ring

theorem hrm_vE2_vXi : hrm D (vE2 D) (vXi D) = 0 := by
  rw [hrm, conjV_vXi, vE2, polar_mk7]
  ring

theorem hrm_vXi_vE3 : hrm D (vXi D) (vE3 D) = 0 := by
  rw [hrm, conjV_vE3, vXi, polar_mk7]
  ring

theorem hrm_vE3_vXi : hrm D (vE3 D) (vXi D) = 0 := by
  rw [hrm, conjV_vXi, vE3, polar_mk7]
  ring

theorem hrm_vE2_vE3 : hrm D (vE2 D) (vE3 D) = 0 := by
  rw [hrm, conjV_vE3, vE2, polar_mk7]
  ring

theorem hrm_vE3_vE2 : hrm D (vE3 D) (vE2 D) = 0 := by
  rw [hrm, conjV_vE2, vE3, polar_mk7]
  ring

theorem polar_vXi_vXi : polar (quadOdd 3 K) (vXi D) (vXi D) = 0 := by
  rw [vXi, polar_mk7]
  linear_combination (2 : K) * D.theta_sq

theorem polar_vE2_vE2 : polar (quadOdd 3 K) (vE2 D) (vE2 D) = 0 := by
  rw [vE2, polar_mk7]
  linear_combination (-2 : K) * D.theta_sq

theorem polar_vE3_vE3 : polar (quadOdd 3 K) (vE3 D) (vE3 D) = 0 := by
  rw [vE3, polar_mk7]
  linear_combination (2 : K) * D.theta_sq

theorem vXi_ne_zero : vXi D ≠ 0 := by
  intro h
  have := congrFun h (.inl 0)
  simp [vXi] at this

theorem vE2_ne_zero : vE2 D ≠ 0 := by
  intro h
  have := congrFun h (.inl 1)
  simp [vE2] at this

theorem tau_polar (x y : W7 K) :
    D.τ (polar (quadOdd 3 K) x y) = polar (quadOdd 3 K) (conjV D x) (conjV D y) := by
  simp only [polar_quadOdd, map_add, map_mul, map_sum, conjV_apply, map_ofNat]

theorem hrm_conj_symm (x y : W7 K) : hrm D x y = D.τ (hrm D y x) := by
  rw [hrm, hrm, tau_polar, conjV_conjV, QuadraticMap.polar_comm]

end Hrm

section Fix

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K)

theorem emb_injective : Function.Injective (emb (F := F) (K := K)) := by
  intro x y h
  funext s
  exact (algebraMap F K).injective (congrFun h s)

theorem theta_ne_zero : D.θ ≠ 0 := by
  intro h
  have := D.theta_sq
  rw [h] at this
  simp at this

theorem two_smul_emb_a :
    (2 : K) • emb (K := K) (mk7 1 0 0 1 0 0 0 : W7 F) = vXi D + conjV D (vXi D) := by
  rw [conjV_vXi, vXi]
  funext t
  rcases t with i | i | u
  · fin_cases i <;> simp [emb, mk7]
    ring
  · fin_cases i <;> simp [emb, mk7]
    ring
  · simp [emb, mk7]

theorem two_theta_smul_emb_b :
    (2 * D.θ) • emb (K := K) (mk7 0 0 0 0 0 0 1 : W7 F) = vXi D - conjV D (vXi D) := by
  rw [conjV_vXi, vXi]
  funext t
  rcases t with i | i | u
  · fin_cases i <;> simp [emb, mk7]
  · fin_cases i <;> simp [emb, mk7]
  · simp [emb, mk7]
    ring

theorem two_smul_emb_c :
    (2 : K) • emb (K := K) (mk7 0 1 0 0 (-1) 0 0 : W7 F) = vE2 D + conjV D (vE2 D) := by
  rw [conjV_vE2, vE2]
  funext t
  rcases t with i | i | u
  · fin_cases i <;> simp [emb, mk7]
    ring
  · fin_cases i <;> simp [emb, mk7]
    ring
  · simp [emb, mk7]

theorem two_theta_smul_emb_d :
    (2 * D.θ) • emb (K := K) (mk7 0 0 1 0 0 (-1) 0 : W7 F) = conjV D (vE2 D) - vE2 D := by
  rw [conjV_vE2, vE2]
  funext t
  rcases t with i | i | u
  · fin_cases i <;> simp [emb, mk7]
    ring
  · fin_cases i <;> simp [emb, mk7]
    ring
  · simp [emb, mk7]

theorem fix_P_of_fix_vXi (h2 : (2 : K) ≠ 0) {g : spinGroup (quadOdd 3 F)}
    (h : actK g (vXi D) = vXi D) :
    spinAction (quadOdd 3 F) g (mk7 1 0 0 1 0 0 0) = mk7 1 0 0 1 0 0 0 ∧
      spinAction (quadOdd 3 F) g (mk7 0 0 0 0 0 0 1) = mk7 0 0 0 0 0 0 1 := by
  have hc : actK g (conjV D (vXi D)) = conjV D (vXi D) := by rw [actK_conjV, h]
  have h2θ : (2 * D.θ : K) ≠ 0 := mul_ne_zero h2 (theta_ne_zero D)
  constructor
  · apply emb_injective (K := K)
    rw [← actK_emb]
    have key : (2 : K) • actK g (emb (K := K) (mk7 1 0 0 1 0 0 0 : W7 F)) =
        (2 : K) • emb (K := K) (mk7 1 0 0 1 0 0 0 : W7 F) := by
      rw [← map_smul, two_smul_emb_a, map_add, h, hc]
    exact smul_right_injective (W7 K) h2 key
  · apply emb_injective (K := K)
    rw [← actK_emb]
    have key : (2 * D.θ) • actK g (emb (K := K) (mk7 0 0 0 0 0 0 1 : W7 F)) =
        (2 * D.θ) • emb (K := K) (mk7 0 0 0 0 0 0 1 : W7 F) := by
      rw [← map_smul, two_theta_smul_emb_b, map_sub, h, hc]
    exact smul_right_injective (W7 K) h2θ key

theorem fix_Pp_of_fix_vE2 (h2 : (2 : K) ≠ 0) {g : spinGroup (quadOdd 3 F)}
    (h : actK g (vE2 D) = vE2 D) :
    spinAction (quadOdd 3 F) g (mk7 0 1 0 0 (-1) 0 0) = mk7 0 1 0 0 (-1) 0 0 ∧
      spinAction (quadOdd 3 F) g (mk7 0 0 1 0 0 (-1) 0) = mk7 0 0 1 0 0 (-1) 0 := by
  have hc : actK g (conjV D (vE2 D)) = conjV D (vE2 D) := by rw [actK_conjV, h]
  have h2θ : (2 * D.θ : K) ≠ 0 := mul_ne_zero h2 (theta_ne_zero D)
  constructor
  · apply emb_injective (K := K)
    rw [← actK_emb]
    have key : (2 : K) • actK g (emb (K := K) (mk7 0 1 0 0 (-1) 0 0 : W7 F)) =
        (2 : K) • emb (K := K) (mk7 0 1 0 0 (-1) 0 0 : W7 F) := by
      rw [← map_smul, two_smul_emb_c, map_add, h, hc]
    exact smul_right_injective (W7 K) h2 key
  · apply emb_injective (K := K)
    rw [← actK_emb]
    have key : (2 * D.θ) • actK g (emb (K := K) (mk7 0 0 1 0 0 (-1) 0 : W7 F)) =
        (2 * D.θ) • emb (K := K) (mk7 0 0 1 0 0 (-1) 0 : W7 F) := by
      rw [← map_smul, two_theta_smul_emb_d, map_sub, h, hc]
    exact smul_right_injective (W7 K) h2θ key

theorem mk7_P_decomp (s z : F) :
    mk7 s 0 0 s 0 0 z = s • (mk7 1 0 0 1 0 0 0 : W7 F) + z • (mk7 0 0 0 0 0 0 1 : W7 F) := by
  funext t
  rcases t with i | i | u
  · fin_cases i <;> simp [mk7]
  · fin_cases i <;> simp [mk7]
  · simp [mk7]

theorem mk7_span_decomp (s a b z : F) :
    mk7 s a b s (-a) (-b) z = s • (mk7 1 0 0 1 0 0 0 : W7 F) + z • (mk7 0 0 0 0 0 0 1 : W7 F) +
      a • (mk7 0 1 0 0 (-1) 0 0 : W7 F) + b • (mk7 0 0 1 0 0 (-1) 0 : W7 F) := by
  funext t
  rcases t with i | i | u
  · fin_cases i <;> simp [mk7]
  · fin_cases i <;> simp [mk7]
  · simp [mk7]

theorem fix_P_all_of_fix_vXi (h2 : (2 : K) ≠ 0) {g : spinGroup (quadOdd 3 F)}
    (h : actK g (vXi D) = vXi D) (s z : F) :
    spinAction (quadOdd 3 F) g (mk7 s 0 0 s 0 0 z) = mk7 s 0 0 s 0 0 z := by
  obtain ⟨h1, h2'⟩ := fix_P_of_fix_vXi D h2 h
  rw [mk7_P_decomp, map_add, map_smul, map_smul, h1, h2']

theorem fix_span_fr0_of_fix {h2F : (2 : F) ≠ 0} (h2 : (2 : K) ≠ 0) {g : spinGroup (quadOdd 3 F)}
    (hξ : actK g (vXi D) = vXi D) (hε : actK g (vE2 D) = vE2 D) :
    ∀ x ∈ (fr0 h2F).span, spinAction (quadOdd 3 F) g x = x := by
  intro x hx
  obtain ⟨s, a, b, z, rfl⟩ := mem_span_fr0 h2F hx
  obtain ⟨h1, h2'⟩ := fix_P_of_fix_vXi D h2 hξ
  obtain ⟨h3, h4⟩ := fix_Pp_of_fix_vE2 D h2 hε
  rw [mk7_span_decomp, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul,
    h1, h2', h3, h4]

end Fix

section HrmLin

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K)

theorem hrm_add_left (x y z : W7 K) : hrm D (x + y) z = hrm D x z + hrm D y z := by
  simp [hrm, QuadraticMap.polar_add_left]

theorem hrm_add_right (x y z : W7 K) : hrm D x (y + z) = hrm D x y + hrm D x z := by
  simp [hrm, conjV_add, QuadraticMap.polar_add_right]

theorem actK_ne_zero {g : spinGroup (quadOdd 3 F)} {x : W7 K} (hx : x ≠ 0) : actK g x ≠ 0 := by
  intro h
  apply hx
  have := congrArg (actK (K := K) g⁻¹) h
  rwa [← actK_mul, inv_mul_cancel, actK_one, map_zero] at this

theorem actK_inv_of_eigen {g : spinGroup (quadOdd 3 F)} {x : W7 K} {c : K}
    (hc : c ≠ 0) (h : actK g x = c • x) : actK g⁻¹ x = c⁻¹ • x := by
  have h' : actK g⁻¹ (actK g x) = x := by rw [← actK_mul, inv_mul_cancel, actK_one]
  rw [h, map_smul] at h'
  calc actK g⁻¹ x = c⁻¹ • (c • actK g⁻¹ x) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = c⁻¹ • x := by rw [h']

end HrmLin

end CFSG.ClassicalInvolution.PhanB3.S
