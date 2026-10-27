module

public import CFSG.GH74.GLS.C3.Layer1.Thm1L32Stable
public import CFSG.GH74.KGroups.Sz8

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.E2
  CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.PumpCalc

namespace CFSG.GH74.GLS.C3.Layer1.Thm1L32

theorem stableTables_proved
    (hG : GenericKnownFacts) (hF : E2ComponentFacts) : StableTables where
  c2shape := fun L _ _ hC hP => c2Shape_of_inC2 hG hF hC hP
  fixedSolv := fun K _ _ h α hα2 hα1 L hL => by
    rcases h with h | h | h | h | h
    · exact KGroups.L28.fixed_solvable h α hα2 hα1 L hL
    · obtain ⟨e⟩ := KGroups.L33.equiv_of_lieModel h
      exact KGroups.L33.fixed_solvable e α hα2 hα1 L hL
    · obtain ⟨e⟩ := KGroups.U33.equiv_of_lieModel h
      exact KGroups.U33.fixed_solvable e α hα2 hα1 L hL
    · obtain ⟨e⟩ := KGroups.Sz8.equiv_of_lieModel h
      exact KGroups.Sz8.fixed_solvable e α hα2 hα1 L hL
    · exact KGroups.M11.fixed_solvable h α hα2 hα1 L hL
  l34rank := fun L _ _ hL34 hcen =>
    (rank3_L3_4 (lieModel_of_center_bot hcen hL34)).not_sectionalTwoRankLE
  sz8three := fun L _ _ h h3 => by
    obtain ⟨-, hc2, hSz⟩ := h
    have hcard : Nat.card L = 58240 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center L), hc2,
        card_of_lieModel_twistedB2 hSz, ordSuzuki_eight]
    rw [hcard] at h3
    revert h3
    norm_num

end CFSG.GH74.GLS.C3.Layer1.Thm1L32
