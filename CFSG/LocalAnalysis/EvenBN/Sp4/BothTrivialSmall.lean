module

public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialClosuresLayer
public import CFSG.LocalAnalysis.SteinbergSFRankOneSelectorSmall
import CFSG.LocalAnalysis.EvenBN.TwoF4.BenderOutcomesExclusions

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

namespace BothTrivialLayer

open Subgroup CFSG.Blueprint
open CFSG.LocalAnalysis.SymplecticFourStandard.RankOneSelector

theorem comm_of_mul_self {D : Type*} [Group D] {E : Subgroup D} (hE : ∀ x ∈ E, x * x = 1) :
    ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
  intro x hx y hy
  have hxy := hE _ (mul_mem hx hy)
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hE x hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hE y hy)
  calc x * y = (y⁻¹ * x⁻¹) := by rw [← mul_inv_rev, inv_eq_of_mul_eq_one_right hxy]
    _ = y * x := by rw [hx', hy']

theorem smallSurvivorsNoElementary :
    SmallSurvivorsNoElementary := by
  have hclass : ∀ {D : Type} [Group D] {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {d p f : ℕ},
      d ≠ 0 → LieModel D t d p f → CFSG.Assembly.LowTwoRank.StatedClassicalModel D t d p f := by
    intro D _ t d p f hd h
    rcases h with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals exact absurd h0 hd
  refine ⟨fun D _ _ hD E hE => ?_, fun D _ hD E hE => ?_⟩
  · have hc := comm_of_mul_self hE
    have hP : IsPGroup 2 E := isPGroup_of_mul_self hE
    rcases hD with h | h | h | h | h | h
    · have := card_le_of_J1 h hP
      omega
    · have := CFSG.GH74.GLS.C3.Layer1.Bk.M12.m12_rank_le_three h E
        (fun a ha => ⟨hE a ha, fun b hb => hc a ha b hb⟩)
      omega
    · have := card_le_of_A7 h hP
      omega
    · have := card_le_of_psl_two_twentyfive (hclass (by norm_num) h) hP
      omega
    · have := (psl_three_five_bounds (hclass (by norm_num) h)).2 E hc hE
      omega
    · have := (psu_three_five_bounds (hclass (by norm_num) h)).2 E hc hE
      omega
  · have := TwoF4.card_le_of_lieModel_G2_three hD (E := E) fun x hx => by
      rw [sq]; exact hE x hx
    omega

end BothTrivialLayer

end CFSG.LocalAnalysis.EvenBN.Sp4
