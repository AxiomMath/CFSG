module

public import CFSG.ClassicalInvolution.Phan.PhanS12Close
public import CFSG.ClassicalInvolution.Phan.PhanS13BLin
public import CFSG.ClassicalInvolution.Phan.PhanS11Adj

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H

section Diag

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K)

theorem exists_vE2_comb_of_lineFix (h2 : (2 : K) ≠ 0) {g : spinGroup (quadOdd 3 F)}
    (hP : PiDetOne D g) (hl : LineFix g (vXi D)) :
    ∃ β γ : K, actK g (vE2 D) = β • vE2 D + γ • vE3 D := by
  obtain ⟨M, -, h0, h1, -⟩ := hP
  obtain ⟨c, hc, e1⟩ := hl
  obtain ⟨a0, b0, c0⟩ := comb_eq_vXi D h2 (h0.symm.trans e1)
  have horth := hrm_actK D g (vE2 D) (vXi D)
  rw [h0, h1, hrm_vE2_vXi, hrm_frame_comb, a0, b0, c0] at horth
  simp only [map_zero, mul_zero, sub_zero, add_zero] at horth
  have hm : M 0 1 = 0 := by
    have : (4 * D.τ c) * M 0 1 = 0 := by linear_combination horth
    exact (mul_eq_zero.mp this).resolve_left
      (mul_ne_zero (four_ne_zero_of h2) (kdat_tau_ne_zero D hc))
  exact ⟨M 1 1, M 2 1, by rw [h1, hm, zero_smul, zero_add]⟩

theorem diag_of_eigen_of_piDetOne (h2 : (2 : K) ≠ 0) {g : spinGroup (quadOdd 3 F)}
    (hP : PiDetOne D g) {l₁ l₂ : K} (h₁ : l₁ ≠ 0) (h₂ : l₂ ≠ 0)
    (e1 : actK g (vXi D) = l₁ • vXi D) (e2 : actK g (vE2 D) = l₂ • vE2 D) :
    ∃ l₃ : K, l₁ * D.τ l₁ = 1 ∧ l₂ * D.τ l₂ = 1 ∧ l₃ * D.τ l₃ = 1 ∧ l₁ * l₂ * l₃ = 1 ∧
      actK g (vE3 D) = l₃ • vE3 D := by
  obtain ⟨M, hdet, h0, h1, h3⟩ := hP
  obtain ⟨a0, b0, c0⟩ := comb_eq_vXi D h2 (h0.symm.trans e1)
  obtain ⟨a1, b1, c1⟩ := comb_eq_vE2 D h2 (h1.symm.trans e2)
  have h4 : (4 : K) ≠ 0 := four_ne_zero_of h2
  have o0 := hrm_actK D g (vE3 D) (vXi D)
  have o1 := hrm_actK D g (vE3 D) (vE2 D)
  rw [h0, h3, hrm_vE3_vXi, hrm_frame_comb, a0, b0, c0] at o0
  rw [h1, h3, hrm_vE3_vE2, hrm_frame_comb, a1, b1, c1] at o1
  simp only [map_zero, mul_zero, sub_zero, add_zero, zero_sub] at o0 o1
  have m02 : M 0 2 = 0 := by
    have : (4 * D.τ l₁) * M 0 2 = 0 := by linear_combination o0
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h4 (kdat_tau_ne_zero D h₁))
  have m12 : M 1 2 = 0 := by
    have : (4 * D.τ l₂) * M 1 2 = 0 := by linear_combination -o1
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h4 (kdat_tau_ne_zero D h₂))
  have e3 : actK g (vE3 D) = M 2 2 • vE3 D := by
    rw [h3, m02, m12, zero_smul, zero_smul, zero_add, zero_add]
  have hd : l₁ * l₂ * M 2 2 = 1 := by
    rw [Matrix.det_fin_three, a0, b0, c0, a1, b1, c1, m02, m12] at hdet
    linear_combination hdet
  exact ⟨M 2 2, norm_one_of_eigen D (isFF7_vXi D h2).2 e1,
    norm_one_of_eigen D (isFF7_vE2 D h2).2 e2, norm_one_of_eigen D (isFF7_vE3 D h2).2 e3, hd, e3⟩

end Diag

end CFSG.ClassicalInvolution.PhanB3.S
