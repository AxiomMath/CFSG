module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.RootData
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint

private theorem iform_expand_right {τ : Tag} (β v : Fin τ.rank → ℤ) :
    iform β v = ∑ j, v j * iform β (Pi.single j 1) := by
  simp only [iform, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem iform_theta_single : ∀ j : Fin Tag.F4.rank,
    iform theta (Pi.single j 1) = if j = 0 then 2 else 0 := by decide +kernel

private theorem iform_alpha1_single :
    iform alpha1 (Pi.single 0 1 : Fin Tag.F4.rank → ℤ) = 4 ∧
    iform alpha1 (Pi.single 1 1 : Fin Tag.F4.rank → ℤ) = -2 ∧
    iform alpha1 (Pi.single 2 1 : Fin Tag.F4.rank → ℤ) = 0 ∧
    iform alpha1 (Pi.single 3 1 : Fin Tag.F4.rank → ℤ) = 0 := by
  decide +kernel

private theorem iform_theta_apply (v : Fin Tag.F4.rank → ℤ) : iform theta v = 2 * v 0 := by
  rw [iform_expand_right]
  simp only [iform_theta_single, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

private theorem iform_alpha1_apply (v : Fin Tag.F4.rank → ℤ) :
    iform alpha1 v = 4 * v 0 - 2 * v 1 := by
  rw [iform_expand_right]
  have h4 : ∀ f : Fin Tag.F4.rank → ℤ, ∑ j, f j = f 0 + f 1 + f 2 + f 3 :=
    fun f => Fin.sum_univ_four f
  obtain ⟨c0, c1, c2, c3⟩ := iform_alpha1_single
  rw [h4, c0, c1, c2, c3]
  ring

set_option linter.unusedSectionVars false



theorem weyl_fixes_S1_F4 {w : WeylGroup Tag.F4} (h : ∀ α ∈ f4LongList, w • α = α) :
    w ∈ parabolicWeylGroup Tag.F4 {i : Fin Tag.F4.rank | i.val = 2 ∨ i.val = 3} := by
  have hθ : w • theta = theta := h _ (by decide +kernel)
  have hα : w • alpha1 = alpha1 := h _ (by decide +kernel)
  rw [← SetLike.mem_coe, (parabolic_Weyl_coordinate_stabilizer Tag.F4
    {i : Fin Tag.F4.rank | i.val = 2 ∨ i.val = 3}).1]
  intro v i hi
  have e1 := iform_smul w theta v
  have e2 := iform_smul w alpha1 v
  rw [hθ, iform_theta_apply, iform_theta_apply] at e1
  rw [hα, iform_alpha1_apply, iform_alpha1_apply] at e2
  fin_cases i
  · show (w • v) 0 = v 0
    omega
  · show (w • v) 1 = v 1
    omega
  · exact absurd (Or.inl rfl) hi
  · exact absurd (Or.inr rfl) hi


end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
