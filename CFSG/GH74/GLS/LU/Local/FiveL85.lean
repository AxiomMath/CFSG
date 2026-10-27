module

public import CFSG.GH74.GLS.LU.Local.FiveL85c
public import CFSG.GH74.GLS.LU.Local.FiveLeaves

public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

theorem leaf85 : Leaf85 := by
  intro G _ _ p f z S K₁ K₂ t u ctx H w₁ b66 X₁ b82 Y b83 v b84
  have c : Cfg4 G p f z S K₁ K₂ t u H w₁ X₁ Y v := ⟨⟨⟨ctx, b66, b82⟩, b83⟩, b84⟩
  refine ⟨c.N_X2_eq, c.R_eq, c.R_card, c.Yw_eq, c.Yw_ab, c.z_inv_R.1, c.z_inv_R.2, ?_⟩
  refine ⟨w₁ * v, c.g_z, Or.inl ⟨?_, ?_⟩⟩
  · rw [X5_eq]; exact cjL_mono _ b82.X₁_syl.1
  · rw [X6_eq]; exact cjL_mono _ c.X2_le_K2

end CFSG.GH74.GLS.LU.Local.Five
