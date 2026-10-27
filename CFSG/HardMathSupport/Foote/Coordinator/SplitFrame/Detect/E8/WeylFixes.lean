module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.RootData
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Defs

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint

private theorem sum8 (f : Fin Tag.E8.rank → ℤ) :
    ∑ j, f j = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 := Fin.sum_univ_eight f

private theorem coeffs5 :
    iform (Pi.single 5 1 : Fin Tag.E8.rank → ℤ) (Pi.single 0 1 : Fin Tag.E8.rank → ℤ) = 0 ∧
    iform (Pi.single 5 1 : Fin Tag.E8.rank → ℤ) (Pi.single 1 1 : Fin Tag.E8.rank → ℤ) = 0 ∧
    iform (Pi.single 5 1 : Fin Tag.E8.rank → ℤ) (Pi.single 2 1 : Fin Tag.E8.rank → ℤ) = 0 ∧
    iform (Pi.single 5 1 : Fin Tag.E8.rank → ℤ) (Pi.single 3 1 : Fin Tag.E8.rank → ℤ) = 0 ∧
    iform (Pi.single 5 1 : Fin Tag.E8.rank → ℤ) (Pi.single 4 1 : Fin Tag.E8.rank → ℤ) = -1 ∧
    iform (Pi.single 5 1 : Fin Tag.E8.rank → ℤ) (Pi.single 5 1 : Fin Tag.E8.rank → ℤ) = 2 ∧
    iform (Pi.single 5 1 : Fin Tag.E8.rank → ℤ) (Pi.single 6 1 : Fin Tag.E8.rank → ℤ) = -1 ∧
    iform (Pi.single 5 1 : Fin Tag.E8.rank → ℤ) (Pi.single 7 1 : Fin Tag.E8.rank → ℤ) = 0 := by
  decide +kernel

private theorem coeffs6 :
    iform (Pi.single 6 1 : Fin Tag.E8.rank → ℤ) (Pi.single 0 1 : Fin Tag.E8.rank → ℤ) = 0 ∧
    iform (Pi.single 6 1 : Fin Tag.E8.rank → ℤ) (Pi.single 1 1 : Fin Tag.E8.rank → ℤ) = 0 ∧
    iform (Pi.single 6 1 : Fin Tag.E8.rank → ℤ) (Pi.single 2 1 : Fin Tag.E8.rank → ℤ) = 0 ∧
    iform (Pi.single 6 1 : Fin Tag.E8.rank → ℤ) (Pi.single 3 1 : Fin Tag.E8.rank → ℤ) = 0 ∧
    iform (Pi.single 6 1 : Fin Tag.E8.rank → ℤ) (Pi.single 4 1 : Fin Tag.E8.rank → ℤ) = 0 ∧
    iform (Pi.single 6 1 : Fin Tag.E8.rank → ℤ) (Pi.single 5 1 : Fin Tag.E8.rank → ℤ) = -1 ∧
    iform (Pi.single 6 1 : Fin Tag.E8.rank → ℤ) (Pi.single 6 1 : Fin Tag.E8.rank → ℤ) = 2 ∧
    iform (Pi.single 6 1 : Fin Tag.E8.rank → ℤ) (Pi.single 7 1 : Fin Tag.E8.rank → ℤ) = -1 := by
  decide +kernel

private theorem coeffs7 :
    iform (Pi.single 7 1 : Fin Tag.E8.rank → ℤ) (Pi.single 0 1 : Fin Tag.E8.rank → ℤ) = 0 ∧
    iform (Pi.single 7 1 : Fin Tag.E8.rank → ℤ) (Pi.single 1 1 : Fin Tag.E8.rank → ℤ) = 0 ∧
    iform (Pi.single 7 1 : Fin Tag.E8.rank → ℤ) (Pi.single 2 1 : Fin Tag.E8.rank → ℤ) = 0 ∧
    iform (Pi.single 7 1 : Fin Tag.E8.rank → ℤ) (Pi.single 3 1 : Fin Tag.E8.rank → ℤ) = 0 ∧
    iform (Pi.single 7 1 : Fin Tag.E8.rank → ℤ) (Pi.single 4 1 : Fin Tag.E8.rank → ℤ) = 0 ∧
    iform (Pi.single 7 1 : Fin Tag.E8.rank → ℤ) (Pi.single 5 1 : Fin Tag.E8.rank → ℤ) = 0 ∧
    iform (Pi.single 7 1 : Fin Tag.E8.rank → ℤ) (Pi.single 6 1 : Fin Tag.E8.rank → ℤ) = -1 ∧
    iform (Pi.single 7 1 : Fin Tag.E8.rank → ℤ) (Pi.single 7 1 : Fin Tag.E8.rank → ℤ) = 2 := by
  decide +kernel

private theorem coeffsθ :
    iform theta (Pi.single 0 1 : Fin Tag.E8.rank → ℤ) = 0 ∧
    iform theta (Pi.single 1 1 : Fin Tag.E8.rank → ℤ) = 0 ∧
    iform theta (Pi.single 2 1 : Fin Tag.E8.rank → ℤ) = 0 ∧
    iform theta (Pi.single 3 1 : Fin Tag.E8.rank → ℤ) = 0 ∧
    iform theta (Pi.single 4 1 : Fin Tag.E8.rank → ℤ) = 0 ∧
    iform theta (Pi.single 5 1 : Fin Tag.E8.rank → ℤ) = 0 ∧
    iform theta (Pi.single 6 1 : Fin Tag.E8.rank → ℤ) = 0 ∧
    iform theta (Pi.single 7 1 : Fin Tag.E8.rank → ℤ) = 1 := by
  decide +kernel

theorem iform_theta_apply (v : Fin Tag.E8.rank → ℤ) : iform theta v = v 7 := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := coeffsθ
  rw [Heis.iform_eq_sum_single, sum8, a0, a1, a2, a3, a4, a5, a6, a7]
  ring

theorem iform_alpha6_apply (v : Fin Tag.E8.rank → ℤ) :
    iform (Pi.single 5 1 : Fin Tag.E8.rank → ℤ) v = 2 * v 5 - v 4 - v 6 := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := coeffs5
  rw [Heis.iform_eq_sum_single, sum8, a0, a1, a2, a3, a4, a5, a6, a7]
  ring

theorem iform_alpha7_apply (v : Fin Tag.E8.rank → ℤ) :
    iform (Pi.single 6 1 : Fin Tag.E8.rank → ℤ) v = 2 * v 6 - v 5 - v 7 := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := coeffs6
  rw [Heis.iform_eq_sum_single, sum8, a0, a1, a2, a3, a4, a5, a6, a7]
  ring

theorem iform_alpha8_apply (v : Fin Tag.E8.rank → ℤ) :
    iform (Pi.single 7 1 : Fin Tag.E8.rank → ℤ) v = 2 * v 7 - v 6 := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := coeffs7
  rw [Heis.iform_eq_sum_single, sum8, a0, a1, a2, a3, a4, a5, a6, a7]
  ring


theorem weyl_fixes_S1_E8 {w : WeylGroup Tag.E8} (hθ : w • theta = theta)
    (h5 : w • (Pi.single 5 1 : Fin Tag.E8.rank → ℤ) = Pi.single 5 1)
    (h6 : w • (Pi.single 6 1 : Fin Tag.E8.rank → ℤ) = Pi.single 6 1)
    (h7 : w • (Pi.single 7 1 : Fin Tag.E8.rank → ℤ) = Pi.single 7 1) :
    w ∈ parabolicWeylGroup Tag.E8 {i : Fin Tag.E8.rank | i.val < 4} := by
  rw [← SetLike.mem_coe, (parabolic_Weyl_coordinate_stabilizer Tag.E8
    {i : Fin Tag.E8.rank | i.val < 4}).1]
  intro v i hi
  have e0 := iform_smul w theta v
  have e5 := iform_smul w (Pi.single 5 1 : Fin Tag.E8.rank → ℤ) v
  have e6 := iform_smul w (Pi.single 6 1 : Fin Tag.E8.rank → ℤ) v
  have e7 := iform_smul w (Pi.single 7 1 : Fin Tag.E8.rank → ℤ) v
  rw [hθ, iform_theta_apply, iform_theta_apply] at e0
  rw [h5, iform_alpha6_apply, iform_alpha6_apply] at e5
  rw [h6, iform_alpha7_apply, iform_alpha7_apply] at e6
  rw [h7, iform_alpha8_apply, iform_alpha8_apply] at e7
  fin_cases i
  · exact absurd (show ((0 : Fin Tag.E8.rank) : ℕ) < 4 by decide) hi
  · exact absurd (show ((1 : Fin Tag.E8.rank) : ℕ) < 4 by decide) hi
  · exact absurd (show ((2 : Fin Tag.E8.rank) : ℕ) < 4 by decide) hi
  · exact absurd (show ((3 : Fin Tag.E8.rank) : ℕ) < 4 by decide) hi
  · show (w • v) 4 = v 4
    omega
  · show (w • v) 5 = v 5
    omega
  · show (w • v) 6 = v 6
    omega
  · show (w • v) 7 = v 7
    omega

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
