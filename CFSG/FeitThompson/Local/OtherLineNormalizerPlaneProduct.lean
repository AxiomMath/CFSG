module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.SigmaCoreTimesPlaneNormalExceptional
import CFSG.FeitThompson.Local.KappaResidualRankTwoExclusion
import CFSG.FeitThompson.Local.SigmaTauThreePrimesDerivedContainment
import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
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

variable {G : Type*} [Group G]

theorem exists_sylow_ge_of_isPGroup_subgroupOf [Finite G] {p : ℕ} [Fact p.Prime] {A T : Subgroup G}
    (hAT : A ≤ T) (hA : IsPGroup p ↥(A.subgroupOf T)) :
    ∃ P : Subgroup G, P ≤ T ∧ Nat.card ↥P = p ^ (Nat.card ↥T).factorization p ∧ A ≤ P := by
  obtain ⟨S, hS⟩ := hA.exists_le_sylow
  refine ⟨(S : Subgroup ↥T).map T.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [Subgroup.card_subtype]; exact S.card_eq_multiplicity
  · have h := Subgroup.map_mono (f := T.subtype) hS
    rwa [Subgroup.map_subgroupOf_eq_of_le hAT] at h

theorem FTS_other_line_normalizer_plane_product
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FPL_low_rank_sylow_central_product.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_other_line_normalizer_plane_product.{u} := by
  intro G _ _ hG M T A A0 p hs
  have : Fintype G := Fintype.ofFinite G
  have hp : p.Prime := hs.prime
  have hfp := Fact.mk hp
  have hT : IsCoatom T := hs.isCoatom_T
  have hAcard : Nat.card ↥A = p ^ 2 := hs.isPlane.natCard
  have hAT : A ≤ T :=
    ((Subgroup.le_centralizer_iff.2
      (hs.le_A.trans
        (Subgroup.le_centralizer_iff_isMulCommutative.2 hs.isPlane.isMulCommutative))).trans
      (Subgroup.centralizer_le_normalizer _)).trans hs.normalizer_le
  refine ⟨hAT, ?_⟩
  by_cases hpσ : p ∈ sigmaPrimes T
  ·
    have hMin : IsOddOrderMinimalSimple G :=
      ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
    have hAS : A ≤ sigmaCore T :=
      le_sigmaCore_of_isPiSubgroup (h₁ G hMin T hT).1 hAT
        (isPiSubgroup_iff.2 fun r hr => by
          rw [hAcard, Nat.primeFactors_pow _ two_ne_zero, hp.primeFactors,
            Finset.mem_singleton] at hr
          exact hr ▸ hpσ)
    rw [sup_eq_left.2 hAS]
    exact le_normalizer_sigmaCore T
  ·
    have hApg : IsPGroup p ↥(A.subgroupOf T) := IsPGroup.of_card (n := 2) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAT).toEquiv]; exact hAcard)
    obtain ⟨P, hPT, hPcard, hAP⟩ := exists_sylow_ge_of_isPGroup_subgroupOf hAT hApg
    have hcfg : IsExceptionalPlaneConfig p T A0 A P :=
      ⟨hT, hp, hpσ, hs.le_A, hAP, hPT, hs.natCard_A0,
        nonempty_mulEquiv_of_isPlaneAt hp hs.isPlane, ⟨hPT, hPcard⟩, hs.normalizer_le⟩
    have hamb : IsFTAmbient G :=
      ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
    have hnormal := FTS_exceptional_normal_plane_product h₁ h₂ h₃ h₄ G hamb p T A0 A P hcfg
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le (sigmaCore_le T) hAT)).1 hnormal

end

end CFSG.FeitThompson.Proofs
