module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Local.CyclicCentralizerFactorRestriction
import CFSG.FeitThompson.Local.NonuniqueLinesAlphaCoreTrivial
import CFSG.FeitThompson.Local.NonuniqueLinesForceSigma
import CFSG.FeitThompson.Local.KappaFixedPrimeCentralizerSylowUnique
import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
import CFSG.FeitThompson.Local.ExceptionalPlaneMaximalElementaryAbelian
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.OddOrder.MaximalOvergroupExistence
import CFSG.FeitThompson.OddOrder.ControlledWitnessCentralTorsion
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

open CFSG.FeitThompson CFSG.FeitThompson.Prep08
  Subgroup

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem coe_subgroupCenterTorsionBy_eq (P : Subgroup G) (p : ℕ) :
    ((subgroupCenterTorsionBy P p : Subgroup G) : Set G)
      = {z | z ∈ P ∧ (∀ y ∈ P, z * y = y * z) ∧ z ^ p = 1} := by
  ext z
  simp only [SetLike.mem_coe, Set.mem_ofPred_eq, mem_subgroupCenterTorsionBy]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, fun y hy => (h2 y hy).symm, h3⟩,
    fun ⟨h1, h2, h3⟩ => ⟨h1, fun y hy => (h2 y hy).symm, h3⟩⟩

theorem natCard_eq_pow_factorization_sigmaCore {p : ℕ} (hp : p.Prime) {M P : Subgroup G}
    (hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p) (hPS : P ≤ sigmaCore M) :
    Nat.card ↥P = p ^ (Nat.card ↥(sigmaCore M)).factorization p := by
  have h1 : (Nat.card ↥M).factorization p ≤ (Nat.card ↥(sigmaCore M)).factorization p :=
    (hp.pow_dvd_iff_le_factorization (Nat.card_pos (α := ↥(sigmaCore M))).ne').1
      (hPcard ▸ Subgroup.card_dvd_of_le hPS)
  have h2 : (Nat.card ↥(sigmaCore M)).factorization p ≤ (Nat.card ↥M).factorization p :=
    (hp.pow_dvd_iff_le_factorization (Nat.card_pos (α := ↥M)).ne').1
      ((Nat.ordProj_dvd _ p).trans (Subgroup.card_dvd_of_le (sigmaCore_le M)))
  rw [hPcard]
  congr 1
  omega

theorem FTS_plane_maximal_overgroups
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₃ : Statements.FTS_nonunique_line_centralizer_bounds.{u})
    (h₄ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FTS_plane_maximal_overgroups.{u} := by
  intro G _ _ hG M A p hM hp hAM hplane
  have := hG.isSimpleGroup
  have hfact := Fact.mk hp
  by_cases hline : ∃ Y : Subgroup G, Y ≤ A ∧ Nat.card ↥Y = p ∧
      normalizer ((Y : Subgroup G) : Set G) ≤ M
  ·
    obtain ⟨Y, hYA, hYcard, hYM⟩ := hline
    exact ⟨centralizer_le_of_le_of_normalizer_le hYA hYM, fun _ => ⟨Y, hYA, hYcard, hYM⟩⟩
  ·
    push Not at hline
    have hsetup : IsNonuniqueLineSetup M A p := by
      refine ⟨hM, hp, hAM, hplane, ?_⟩
      intro Y hYA hYcard
      have hYbot : Y ≠ ⊥ := by
        rintro rfl
        rw [Subgroup.card_bot] at hYcard
        exact hp.one_lt.ne hYcard
      have hYp : IsPGroup p ↥Y := IsPGroup.of_card (by rw [hYcard, pow_one])
      have hlt : normalizer ((Y : Subgroup G) : Set G) < ⊤ :=
        normalizer_lt_top_of_isPGroup hG.not_isMulCommutative hp hYbot hYp
      obtain ⟨T, hT, hTle⟩ := exists_isCoatom_ge_of_ne_top hlt.ne
      exact ⟨T, hT, fun h => hline Y hYA hYcard (h ▸ hTle), hTle⟩
    have hpσ : p ∈ sigmaPrimes M :=
      FTS_nonunique_lines_force_sigma h₁ h₂ h₃ h₄ G hG M A p hsetup
    obtain ⟨-, hnil, hZ⟩ := FTS_nonunique_lines_alpha_core_trivial h₃ G hG M A p hsetup
    obtain ⟨P, hPsyl, hAP⟩ :=
      exists_isSylowOf_ge hp hAM (IsPGroup.of_card hplane.natCard)
    obtain ⟨hZ0bot, hZ0A, -, -⟩ :=
      hZ P hPsyl hAP (subgroupCenterTorsionBy P p) (coe_subgroupCenterTorsionBy_eq P p)
    have hPM := hPsyl.le
    have hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p :=
      (isSylowOf_iff_natCard hp hPM).1 hPsyl
    let _ : Fintype G := Fintype.ofFinite G
    have hG2 : CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
      ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
    obtain ⟨hHallOf, -, -⟩ := h₁ G hG2 M hM
    have hPS : P ≤ sigmaCore M :=
      le_sigmaCore_of_isPiSubgroup_of_isHallPiSubgroup hHallOf.2 hPM
        (isPiSubgroup_of_natCard_eq_pow hp hPcard hpσ)
    have hScard := natCard_eq_pow_factorization_sigmaCore hp hPcard hPS
    have hMN : M ≤ normalizer ((subgroupCenterTorsionBy P p : Subgroup G) : Set G) :=
      le_normalizer_subgroupCenterTorsionBy (L := M) hnil (sigmaCore_le M)
        (sigmaCore_normal_subgroupOf M) hPS hScard le_rfl
    have hNeq : normalizer ((subgroupCenterTorsionBy P p : Subgroup G) : Set G) = M :=
      normalizer_eq_of_isCoatom hM hZ0bot (hZ0A.trans hAM) hMN
    exact ⟨centralizer_le_of_le_of_normalizer_le hZ0A hNeq.le, fun hpn => absurd hpσ hpn⟩

end

end CFSG.FeitThompson.Proofs
