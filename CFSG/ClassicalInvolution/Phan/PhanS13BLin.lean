module

public import CFSG.ClassicalInvolution.Phan.PhanS10Vec

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H

section Lin

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K)

theorem frame_comb_unique (h2 : (2 : K) ≠ 0) {α β γ α' β' γ' : K}
    (h : α • vXi D + β • vE2 D + γ • vE3 D = α' • vXi D + β' • vE2 D + γ' • vE3 D) :
    α = α' ∧ β = β' ∧ γ = γ' := by
  have e0 := congrFun h (.inl 0)
  have e1 := congrFun h (.inl 1)
  have e2 := congrFun h (.inl 2)
  simp [vXi, vE2, vE3, mk7] at e0 e1 e2
  have e3 : D.θ * ((γ - β) - (γ' - β')) = 0 := by linear_combination e2
  have e4 : (γ - β) - (γ' - β') = 0 := (mul_eq_zero.mp e3).resolve_left (theta_ne_zero D)
  have e5 : 2 * (γ - γ') = 0 := by linear_combination e1 + e4
  have e6 : γ - γ' = 0 := (mul_eq_zero.mp e5).resolve_left h2
  exact ⟨e0, by linear_combination e1 - e6, by linear_combination e6⟩

theorem comb_eq_vXi (h2 : (2 : K) ≠ 0) {α β γ l : K}
    (h : α • vXi D + β • vE2 D + γ • vE3 D = l • vXi D) : α = l ∧ β = 0 ∧ γ = 0 :=
  frame_comb_unique D h2 (α' := l) (β' := 0) (γ' := 0) (by rw [h]; simp)

theorem comb_eq_vE2 (h2 : (2 : K) ≠ 0) {α β γ l : K}
    (h : α • vXi D + β • vE2 D + γ • vE3 D = l • vE2 D) : α = 0 ∧ β = l ∧ γ = 0 :=
  frame_comb_unique D h2 (α' := 0) (β' := l) (γ' := 0) (by rw [h]; simp)

theorem hrm_frame_comb (α β γ α' β' γ' : K) :
    hrm D (α • vXi D + β • vE2 D + γ • vE3 D) (α' • vXi D + β' • vE2 D + γ' • vE3 D) =
      4 * α * D.τ α' - 4 * β * D.τ β' + 4 * γ * D.τ γ' := by
  simp only [hrm_add_left, hrm_add_right, hrm_smul_left, hrm_smul_right, hrm_vXi_vXi,
    hrm_vE2_vE2, hrm_vE3_vE3, hrm_vXi_vE2, hrm_vXi_vE3, hrm_vE2_vXi, hrm_vE2_vE3, hrm_vE3_vXi,
    hrm_vE3_vE2]
  ring

theorem kdat_tau_ne_zero {c : K} (hc : c ≠ 0) : D.τ c ≠ 0 := fun h =>
  hc (by rw [← D.tau_tau c, h, map_zero])

theorem norm_one_of_eigen {g : spinGroup (quadOdd 3 F)} {x : W7 K} {l : K}
    (hx : hrm D x x ≠ 0) (h : actK g x = l • x) : l * D.τ l = 1 := by
  have h1 := hrm_actK D g x x
  rw [h, hrm_smul_left, hrm_smul_right, ← mul_assoc] at h1
  have : (l * D.τ l - 1) * hrm D x x = 0 := by linear_combination h1
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hx)

end Lin

end CFSG.ClassicalInvolution.PhanB3.S
