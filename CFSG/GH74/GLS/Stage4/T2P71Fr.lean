module

public import CFSG.GH74.GLS.Stage4.T2P71FrD

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.Stage4.Rest.T2

theorem p71Frattini_proved : P71Frattini := by
  intro G _ _ Gs _ n N u hE hnotsyl
  have h := hE.ctx
  have h' := hE.swap.ctx
  obtain ⟨t, htR, htX, htc⟩ := T6.P71.p71Frattini_core h h' hnotsyl
  have hX₂R : N.X₂ ≤ T6.R₂ N 3 := T6.X₂_le_R₂ h
  refine ⟨lt_of_le_of_ne hX₂R (fun heq => htX (heq ▸ htR)), ?_⟩
  have hX₂C : N.X₂ ≤ T6.R₂ N 3 ⊓ Subgroup.centralizer (N.X₁ : Set G) := by
    refine le_inf hX₂R (fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => ?_)
    have hxK : x ∈ N.K₂ := by rw [hE.sec5.loc.K₂_eq]; exact Subgroup.mem_sup_left hx
    have hyK : y ∈ N.K₁ := by rw [hE.sec5.loc.K₁_eq]; exact Subgroup.mem_sup_left hy
    exact hE.sec5.loc.K_comm y hyK x hxK
  refine lt_of_le_of_ne hX₂C (fun heq => htX ?_)
  rw [heq]
  exact ⟨htR, Subgroup.mem_centralizer_iff.2 fun y hy => (htc y hy).symm⟩

end CFSG.GH74.GLS.Stage4.Rest
