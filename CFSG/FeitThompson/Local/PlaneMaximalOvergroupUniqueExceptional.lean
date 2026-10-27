module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.SigmaCoreNilpotentExceptionalPlane
import CFSG.FeitThompson.Local.SigmaCoreConjugateTrivialExceptionalPlane
import CFSG.FeitThompson.Local.NilpotentSigmaPrimeSeparation
import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson
open Subgroup Pointwise

universe u

variable {G : Type*} [Group G]

theorem conjBy_eq_conjSubgroup (Y : Subgroup G) (g : G) :
    conjBy Y g = Prep08.conjSubgroup Y g := (rfl)

theorem conjBy_eq_self_of_mem {M : Subgroup G} {g : G} (hg : g ∈ M) : conjBy M g = M :=
  Subgroup.conj_smul_eq_self_of_mem (inv_mem hg)

theorem eq_of_mem_of_eq_conjSubgroup {M T : Subgroup G} {g : G}
    (hT : T = Prep08.conjSubgroup M g) (hg : g ∈ M) : T = M := by
  rw [hT, ← conjBy_eq_conjSubgroup, conjBy_eq_self_of_mem hg]

theorem FTS_exceptional_core_overgroup_uniqueness
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FTS_exceptional_core_overgroup_uniqueness.{u} := by
  intro G _ _ hG p M A₀ A P hc T hT hAT hne
  have hM : IsCoatom M := hc.isCoatom
  have hTc : IsCoatom T := hT
  have hMin8 : Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable⟩
  have hnil : Group.IsNilpotent ↥(sigmaCore M) :=
    FTS_exceptional_core_nilpotent h₁ h₂ G hG p M A₀ A P hc
  obtain ⟨g, hg⟩ : ∃ g : G, T = Prep08.conjSubgroup M g := by
    by_contra h
    push Not at h
    exact hne (FTS_nilpotent_sigma_prime_separation G hMin8 M T hM hTc h hnil).2
  by_cases hgM : g ∈ M
  · exact eq_of_mem_of_eq_conjSubgroup hg hgM
  ·
    refine absurd ?_ hne
    have hAMg : A ≤ conjBy M g := by rw [conjBy_eq_conjSubgroup, ← hg]; exact hAT
    obtain ⟨hint, -⟩ :=
      FTS_exceptional_core_conjugate_intersection h₁ h₂ G hG p M A₀ A P hc g hgM hAMg
    refine le_bot_iff.1 (le_trans (le_trans (inf_le_inf_left _ (sigmaCore_le T)) ?_) hint.le)
    rw [hg, ← conjBy_eq_conjSubgroup]

end

end CFSG.FeitThompson.Proofs
