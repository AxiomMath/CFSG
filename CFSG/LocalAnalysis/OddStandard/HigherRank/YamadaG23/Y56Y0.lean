module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54Two
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56Phi

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y56_phi_inv {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {y : G}
    (hy : y ∈ e4Y s) : f3phi s y⁻¹ = (f3phi s y)⁻¹ := by
  have h := y56_phi_mul hH y hy y⁻¹ ((e4Y s).inv_mem hy)
  have h1 : f3phi s (y * y⁻¹) = 1 := by
    rw [mul_inv_cancel]
    simp [f3phi]
  rw [h1] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem y56_y0_B_fix (c : Ctx5 G L) (hH : F33Hyp c.s c.e) {y₀ : G} (hy₀ : IsY0 c.s y₀) :
    ∀ b ∈ c.s.fr.B, ⁅b, y₀⁆ ∈ e4Q c.s := by
  intro b hb
  have hbC₂ : b ∈ c.s.C₂ := y56_B_le_C2 hH hb
  have hcomm : ⁅b, y₀⁆ ∈ cen c.s.fr.B := y56_C2_comm c hH b hbC₂ y₀ hy₀.1
  exact Subgroup.mem_sup_left (y56_V_le_E hH hcomm)

theorem y56_y0_a (c : Ctx5 G L) (hH : F33Hyp c.s c.e) {y₀ : G} (hy₀ : IsY0 c.s y₀) :
    c.d⁻¹ * ⁅y5a c.s, y₀⁆ ∈ e4Q c.s := by
  have haNE : y5a c.s ∈ normIn L c.s.fr.E := y56_A_le_NE hH (y5a_mem_A c.s)
  have haN : y5a c.s ∈ e4N c.s := y56_NL_le_N hH haNE
  have haNB : y5a c.s ∈ normIn L c.s.fr.B := y5a_mem_normB hH
  have haNBH : y5a c.s ∈ normIn c.s.H c.s.fr.B :=
    Subgroup.mem_inf.mpr
      ⟨s3_L_le_H c.s hH.hS (Subgroup.mem_inf.mp haNB).1, (Subgroup.mem_inf.mp haNB).2⟩
  have hy₀C₂ : y₀ ∈ c.s.C₂ := hy₀.1
  have hy₀Y : y₀ ∈ e4Y c.s := y56_y0_mem_Y hH hy₀
  have hdY : c.d ∈ e4Y c.s := y56_d_mem_Y c hH
  have haYaC₂ : y5a c.s * y₀ * (y5a c.s)⁻¹ ∈ c.s.C₂ :=
    y56_NB_norm_C2 hH (y5a c.s) haNBH y₀ hy₀C₂
  have haYaY : y5a c.s * y₀ * (y5a c.s)⁻¹ ∈ e4Y c.s :=
    y56_N_norm_Y hH (y5a c.s) haN y₀ hy₀Y
  have huC₂ : ⁅y5a c.s, y₀⁆ ∈ c.s.C₂ :=
    (c.s.C₂).mul_mem haYaC₂ ((c.s.C₂).inv_mem hy₀C₂)
  have huY : ⁅y5a c.s, y₀⁆ ∈ e4Y c.s :=
    (e4Y c.s).mul_mem haYaY ((e4Y c.s).inv_mem hy₀Y)
  have hd2 : c.d * c.d = 1 := by rw [← pow_two]; exact y5_d_sq c
  have hphid : f3phi c.s c.d⁻¹ = c.s.fr.z := by
    rw [inv_eq_of_mul_eq_one_right hd2]
    exact y56_phi_d c hH
  have hphia : f3phi c.s (y5a c.s * y₀ * (y5a c.s)⁻¹) = c.s.fr.z * y56v0 c.s := by
    rw [y56_phi_conj hH (y5a c.s) haN y₀, y56_phi_y0 hy₀, y5a_conj_w hH]
  have hphiu : f3phi c.s ⁅y5a c.s, y₀⁆ = c.s.fr.z := by
    rw [commutatorElement_def,
      y56_phi_mul hH _ haYaY _ ((e4Y c.s).inv_mem hy₀Y), hphia,
      y56_phi_inv hH hy₀Y, y56_phi_y0 hy₀]
    group
  have hz2 : c.s.fr.z * c.s.fr.z = 1 := by
    have h := y56_E_sq hH c.s.fr.z (y56_z_mem_E hH)
    rwa [pow_two] at h
  have hphi1 : f3phi c.s (c.d⁻¹ * ⁅y5a c.s, y₀⁆) = 1 := by
    rw [y56_phi_mul hH c.d⁻¹ ((e4Y c.s).inv_mem hdY) _ huY, hphid, hphiu, hz2]
  have hX0 : c.d⁻¹ * ⁅y5a c.s, y₀⁆ ∈ e4X0 c.s :=
    (y56_phi_eq_one hH (c.d⁻¹ * ⁅y5a c.s, y₀⁆) ((e4Y c.s).mul_mem
      ((e4Y c.s).inv_mem hdY) huY)).mp hphi1
  have hQ : c.d⁻¹ * ⁅y5a c.s, y₀⁆ ∈ c.s.C₂ ⊓ e4X0 c.s :=
    Subgroup.mem_inf.mpr
      ⟨(c.s.C₂).mul_mem ((c.s.C₂).inv_mem (y54_d_mem_C2 c hH)) huC₂, hX0⟩
  simpa only [y56_C2_inf_X0 hH] using hQ

end CFSG.OddStandard.HigherRank.YamadaG23
