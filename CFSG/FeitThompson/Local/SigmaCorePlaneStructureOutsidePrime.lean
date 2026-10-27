module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.PlaneMaximalOvergroups
import CFSG.FeitThompson.Local.SigmaCoreNilpotentExceptionalPlane
import CFSG.FeitThompson.Local.ExceptionalPlaneFixedFreeLines
import CFSG.FeitThompson.Local.SigmaCoreTimesPlaneNormalExceptional
import CFSG.FeitThompson.Local.NonuniqueLinesAlphaCoreTrivial
import CFSG.FeitThompson.Local.KappaResidualRankTwoExclusion
import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
public import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson
open Subgroup

universe u

theorem FTS_outside_sigma_plane_structure
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₃ : Statements.FPL_low_rank_sylow_central_product.{u})
    (h₄ : Statements.FTS_nonunique_line_centralizer_bounds.{u})
    (h₅ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FTS_outside_sigma_plane_structure.{u} := by
  intro G _ _ hG M A p hM hp hpσ hAM hA
  have hG7 : IsFTAmbient G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hAplane7 : IsElementaryAbelianPlane p A := nonempty_mulEquiv_of_isPlaneAt hp hA
  obtain ⟨A₀, hA₀A, hA₀card, hNA₀⟩ :=
    (FTS_plane_maximal_overgroups h₁ h₂ h₄ h₅ G hG M A p hM hp hAM hA).2 hpσ
  obtain ⟨P, hPsyl, hAP⟩ := exists_isSylowOf_ge hp hAM (IsPGroup.of_card hA.natCard)
  have hPM : P ≤ M := hPsyl.le
  have hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p :=
    (Prep08.isSylowOf_iff_natCard hp hPM).1 hPsyl
  have hc : IsExceptionalPlaneConfig p M A₀ A P :=
    ⟨hM, hp, hpσ, hA₀A, hAP, hPM, hA₀card, hAplane7, ⟨hPM, hPcard⟩, hNA₀⟩
  refine ⟨FTS_exceptional_core_nilpotent h₁ h₅ G hG7 p M A₀ A P hc,
    (FTS_exceptional_plane_fixed_free_lines h₁ h₃ h₅ G hG7 p M A₀ A P hc).2.1, ?_⟩
  have hle : sigmaCore M ⊔ A ≤ M := sup_le (sigmaCore_le M) hAM
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).1
    (FTS_exceptional_normal_plane_product h₁ h₂ h₃ h₅ G hG7 p M A₀ A P hc)

end

end CFSG.FeitThompson.Proofs
