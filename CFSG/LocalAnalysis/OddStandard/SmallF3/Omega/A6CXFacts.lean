module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFShapes
public import CFSG.Adapters.StatedPSLTwoNine

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem a6c_X_facts {G : Type} [Group G] [Finite G] {X : Subgroup G} (hX : IsQuasisimple ↥X)
    (h : IsL29 X) :
    Nonempty (↥X ⧸ center ↥X ≃* alternatingGroup (Fin 6)) ∧ Odd (Nat.card (center ↥X)) := by
  have hs : IsSimpleGroup (↥X ⧸ oddCore ↥X) := (ff_simple_of_lieModel_psl2 h).1
  have hc : center ↥X = oddCore ↥X := center_eq_oddCore_of_simple hX hs
  have hlie : LieModel (↥X ⧸ center ↥X) .PSL 2 3 2 :=
    LieModel.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hc).symm h
  refine ⟨CFSG.Open.StatedAPI.nonempty_mulEquiv_alternating_six_of_psl_two_nine
    (hlie.statedClassicalModel_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0)), ?_⟩
  rw [hc]
  exact ff_odd_card_oddCore ↥X

end CFSG.OddStandard.SmallF3.Omega
