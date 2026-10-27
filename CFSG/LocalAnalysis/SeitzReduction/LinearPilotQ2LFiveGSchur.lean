module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplitSmall
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindLinearCentre

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint
open CFSG.SeitzReduction.F4Pilot (OddSchurTrivial)

theorem nonempty_projectiveSL_four_mulEquiv_of_card_four {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) :
    Nonempty (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 4 K ≃*
      Matrix.SpecialLinearGroup (Fin 4) K) := by
  have hZ : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 4 K = ⊥ := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center]
    exact SymplecticPilot.center_specialLinear_eq_bot_of_coprime (by rw [hK]; decide)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot⟩

theorem oddSchurTrivial_of_lieModel_PSL_four_four
    {X : Type} [Group X]
    (hX : LieModel X .PSL 4 2 2) : OddSchurTrivial X := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_projectiveSL_equiv_of_lieModel_PSL hX
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have : CharP K 2 := SeitzQ2.charTwo_of_natCard_eq_two_pow hK
  obtain ⟨φ⟩ := nonempty_projectiveSL_four_mulEquiv_of_card_four hK4
  exact (SeitzQ2.oddSchurTrivial_specialLinearGroup 3 K).of_mulEquiv (e.trans φ).symm

end CFSG.SeitzReduction.LinearPilot
