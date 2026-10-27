module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.RegularFirstPlaneFixedLineEscape
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing
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

open CFSG.FeitThompson Subgroup

universe u

theorem FNI_tau13_nonregular_line_normalizer_sigma
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_full_central_hall.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_nonabelian_ambient_unique_nonregular_line.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FNI_tau13_nonsigma_normalizer_reflected_plane.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_tau13_nonregular_line_normalizer_sigma.{u} := by
  intro G _ _ hG M E hsc p hp P hPE hPcard hPS L hL hNL
  by_contra hpL
  obtain ⟨⟨F, hLF, q, hq, Q, hQF, hQcard, A, hAF, hplane, hPA, hCA, hAQ, hSQ⟩, hp2⟩ :=
    h₆ G hG M E hsc p hp P hPE hPcard hPS L hL hNL hpL
  have hG04 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hLF04 : _root_.CFSG.FeitThompson.IsSigmaComplement L F := ⟨hLF.isCoatom, hLF.semidirect⟩
  have hpp : p.Prime := prime_of_mem_tauTwoPrimes hp2
  have hplane04 : _root_.CFSG.FeitThompson.IsElementaryAbelianPlane p A := by
    refine nonempty_mulEquiv_pi_of_isElementaryAbelian hpp ?_ hplane.2
    exact isElementaryAbelian_iff.2 (isElementaryAbelianSubgroup_iff.1 hplane.1)
  have hesc := FNI_regular_first_plane_fixed_line_escape h₁ h₂ h₃ h₄ h₅ h₇ h₈ G hG04 p q L F A Q
    hLF04 hp2 hAF hplane04 hq hQF hQcard hSQ hAQ
  have hkey := hesc.2.2.2.2
  rw [CFSG.FeitThompson.Prep05.centralizerIn_eq] at hCA
  rw [hCA] at hkey
  exact hkey ((Subgroup.centralizer_le_normalizer (P : Set G)).trans hNL)

end

end CFSG.FeitThompson.Proofs
