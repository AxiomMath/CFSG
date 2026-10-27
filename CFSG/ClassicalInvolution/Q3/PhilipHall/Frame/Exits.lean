module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Q8Target
public import CFSG.RankThree.Classical.SteinbergR3EHigherSymplecticOuterOrder
public import CFSG.Assembly.GL83LieDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem eq_top_of_inner_eq_top {Y : Type*} [Group Y] {T : Subgroup Y} [T.Normal]
    (hC : Subgroup.centralizer (T : Set Y) = ⊥) (hinn : inner ↥T = ⊤) : T = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have hmem : MulAut.conjNormal y ∈ inner ↥T := hinn ▸ Subgroup.mem_top _
  obtain ⟨s, hs⟩ := hmem
  have hcent : (s : Y)⁻¹ * y ∈ Subgroup.centralizer (T : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have h1 := congrArg (fun φ : MulAut ↥T => ((φ ⟨t, ht⟩ : ↥T) : Y)) hs
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      MulAut.conjNormal_apply] at h1
    calc t * ((s : Y)⁻¹ * y) = (s : Y)⁻¹ * ((s : Y) * t * (s : Y)⁻¹) * y := by group
      _ = (s : Y)⁻¹ * (y * t * y⁻¹) * y := by rw [h1]
      _ = (s : Y)⁻¹ * y * t := by group
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hcent
  exact hcent ▸ s.2

theorem inner_eq_top_of_lieModel_psp_three_two {S : Type} [Group S]
    (h : Models.LieModel S .PSp 3 2 1) : inner S = ⊤ := by
  have hcl : CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSp 3 2 1 := by
    rcases h.2 with hc | ⟨h0, -⟩
    · exact hc
    · exact absurd h0 (by norm_num)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hcl
  have hout : Nat.card (Outer S) = 1 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    simpa using (CFSG.RankThree.Classical.higher_symplectic_outer_order_divides_field_multiplier_bound
      Nat.prime_two le_rfl le_rfl hK).1
  exact Subgroup.index_eq_one.mp hout

theorem frameExitSp62_proved : FrameExitSp62 := by
  intro Y _ _ T hT hC hsp
  exact eq_top_of_inner_eq_top hC (inner_eq_top_of_lieModel_psp_three_two hsp)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
