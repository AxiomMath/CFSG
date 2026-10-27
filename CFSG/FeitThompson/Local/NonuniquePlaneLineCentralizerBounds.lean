module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.CommutatorSigmaCoreMeetOtherLineTrivial
import CFSG.FeitThompson.Local.OtherLineNormalizerAlphaCentralization
import CFSG.FeitThompson.Local.SigmaTauThreePrimesDerivedContainment
import CFSG.FeitThompson.Local.AlphaPrimesInSigmaPrimes
import CFSG.FeitThompson.Local.RegularTauAlphaCentralizerRankBounds
import CFSG.FeitThompson.Local.CriticalRegularComplementFixedPoints
import CFSG.FeitThompson.OddOrder.RankThreeUniquenessMaximalOvergroup
import CFSG.FeitThompson.Definitions.AlphaCore
import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
import CFSG.FeitThompson.Definitions.MaximumElementaryAbelianPrimeRank
import CFSG.FeitThompson.Definitions.LocalComplementaryPrimeConstraint
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
open CFSG.FeitThompson.Prep08
open Subgroup

universe u

variable {G : Type*} [Group G]

theorem elementaryAbelianPRank_le_two_of_le_of_le [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) {M T X : Subgroup G}
    (hM : IsCoatom M) (hT : IsCoatom T) (hMT : M ≠ T) (hXM : X ≤ M) (hXT : X ≤ T) (r : ℕ) :
    elementaryAbelianPRank r ↥X ≤ 2 := by
  refine elementaryAbelianPRank_le_of_forall_prime (fun s hs => ?_) r
  by_contra hcon
  have h3 : 3 ≤ elementaryAbelianPRank s ↥X := by omega
  have hXtop : X ≠ ⊤ := fun h => hM.1 (top_le_iff.1 (h ▸ hXM))
  obtain ⟨N, -, huniq⟩ := existsUnique_isCoatom_ge_of_three_le_maxElementaryAbelianPRank
    hna hodd hsolv hXtop (h3.trans (elementaryAbelianPRank_le_maxElementaryAbelianPRank hs))
  exact hMT (by rw [huniq M ⟨hM, hXM⟩, huniq T ⟨hT, hXT⟩])

theorem FTS_nonunique_line_centralizer_bounds
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FPL_low_rank_sylow_central_product.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_nonunique_line_centralizer_bounds.{u} := by
  intro G _ _ hG M A p hs
  have : Fintype G := Fintype.ofFinite G
  have hsimple : IsSimpleGroup G := hG.isSimpleGroup
  have hp : p.Prime := hs.prime
  have hM : IsCoatom M := hs.isCoatom_M
  have hAcard : Nat.card ↥A = p ^ 2 := hs.isPlane.natCard
  have hMin : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hrank : ∀ {T X : Subgroup G}, IsCoatom T → T ≠ M → X ≤ M → X ≤ T →
      ∀ r : ℕ, elementaryAbelianPRank r ↥X ≤ 2 := fun hT hTM hXM hXT r =>
    elementaryAbelianPRank_le_two_of_le_of_le hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hM hT (Ne.symm hTM) hXM hXT r
  have hsigma : p ∉ sigmaPrimes M → ∀ Y ≤ A, Nat.card ↥Y = p →
      sigmaCore M ⊓ centralizer ((Y : Subgroup G) : Set G) ≤
        M ⊓ centralizer ((A : Subgroup G) : Set G) := by
    intro hpσ Y hYA hYcard
    obtain ⟨T, hT, hTM, hNT⟩ := hs.nonunique Y hYA hYcard
    have hsetup : IsOtherLineSetup M T A Y p :=
      ⟨hM, hT, Ne.symm hTM, hp, hs.le, hs.isPlane, hYA, hYcard, hNT⟩
    have hcomm := FTS_other_line_normalizer_sigma_centralization h₁ h₂ h₃ h₄ G hG M T A Y p
      hsetup hpσ
    have hCT : centralizer ((Y : Subgroup G) : Set G) ≤ T :=
      (Subgroup.centralizer_le_normalizer _).trans hNT
    have h2 : sigmaCore M ⊓ T ≤ centralizer ((A : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1
        (by rw [Subgroup.commutator_comm]; exact hcomm)
    exact le_inf (inf_le_left.trans (sigmaCore_le M)) ((inf_le_inf_left _ hCT).trans h2)
  refine ⟨?_, hsigma, ?_, ?_⟩
  ·
    intro Y hYA hYcard r
    obtain ⟨T, hT, hTM, hNT⟩ := hs.nonunique Y hYA hYcard
    exact hrank hT hTM inf_le_left
      (inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans hNT)) r
  ·
    intro hpα Y hYA hYcard
    obtain ⟨T, hT, hTM, hNT⟩ := hs.nonunique Y hYA hYcard
    have hCT : centralizer ((Y : Subgroup G) : Set G) ≤ T :=
      (Subgroup.centralizer_le_normalizer _).trans hNT
    by_cases hpσ : p ∈ sigmaPrimes M
    · have hsetup : IsOtherLineSetup M T A Y p :=
        ⟨hM, hT, Ne.symm hTM, hp, hs.le, hs.isPlane, hYA, hYcard, hNT⟩
      have hcomm := FTS_other_line_normalizer_alpha_centralization h₁ h₂ h₃ h₄ G hG M T A Y p
        hsetup hpσ hpα
      have h2 : alphaCoreOf M ⊓ T ≤ centralizer ((A : Subgroup G) : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.1
          (by rw [Subgroup.commutator_comm]; exact hcomm)
      exact le_inf (inf_le_left.trans (alphaCoreOf_le M)) ((inf_le_inf_left _ hCT).trans h2)
    ·
      have hBS : alphaCoreOf M ≤ sigmaCore M :=
        le_sigmaCore_of_isPiSubgroup (h₁ G hMin M hM).1 (alphaCoreOf_le M)
          ((isPiSubgroup_map_subtype_iff.2 (isPiSubgroup_alphaCore ↥M)).mono
            (alphaPrimes_subset_sigmaPrimes hG.not_isMulCommutative hG.odd_natCard
              hG.isSolvable_of_ne_top hM))
      exact (inf_le_inf_right _ hBS).trans (hsigma hpσ Y hYA hYcard)
  ·
    intro r
    have hApg : IsPGroup p ↥A := IsPGroup.of_card (n := 2) hAcard
    have hAne : A ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hAcard
      rcases Nat.pow_eq_one.1 hAcard.symm with h1 | h2
      · exact hp.ne_one h1
      · omega
    obtain ⟨Y, hYA, hYcard⟩ := exists_le_natCard_eq_prime hp hApg hAne
    obtain ⟨T, hT, hTM, hNT⟩ := hs.nonunique Y hYA hYcard
    refine hrank hT hTM inf_le_left (inf_le_right.trans ?_) r
    exact (Subgroup.centralizer_le (by exact_mod_cast hYA)).trans
      ((Subgroup.centralizer_le_normalizer _).trans hNT)

end

end CFSG.FeitThompson.Proofs
