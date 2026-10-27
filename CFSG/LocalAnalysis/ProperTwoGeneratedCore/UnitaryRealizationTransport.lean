module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryAutomorphismHermitian
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNoncentralPairActionUnitary

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open Matrix CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ProperTwoGeneratedCore.LocalCriterionNoncentralPairAction

theorem unitaryAutomorphismRealization : UnitaryAutomorphismRealization := by
  intro K _ _ J f hf hcard hfixed hJ β
  have hq : 2 < 2 ^ f := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right two_pos hf)
  obtain ⟨σ, A, hA, hβ⟩ := exists_isometry_psu_of_card Nat.prime_two hq hcard hfixed hJ β
  refine ⟨σ, A, hA, fun g => ?_⟩
  obtain ⟨hg, hβg⟩ := hβ g
  have hmap : GeneralLinearGroup.map σ.toRingHom (g : GL (Fin 3) K) = glAut σ (g : GL (Fin 3) K) :=
    Units.ext rfl
  rw [hmap]
  exact congrArg Subtype.val hβg

end CFSG.ProperTwoGeneratedCore.HighRankPair
