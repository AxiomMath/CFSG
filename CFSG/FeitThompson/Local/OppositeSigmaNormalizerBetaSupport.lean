module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.SigmaPrimeNormalizerOutsideNarrowPrimeFactor
import CFSG.FeitThompson.Local.SigmaPrimeNormalizerEmbeddingSylows
import CFSG.FeitThompson.Local.SigmaComplementExistsNontrivial
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.DisjointDSetsNonconjugateMaximals
import CFSG.FeitThompson.Local.BetaPrimesSigmaCompatibility
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson CFSG.FeitThompson

universe u

variable {G : Type u} [Group G]

theorem dvd_natCard_sigmaComplement [Finite G] {M E : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hE : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E) (hpM : p ∣ Nat.card ↥M)
    (hpS : ¬ p ∣ Nat.card ↥(sigmaCore M)) : p ∣ Nat.card ↥E := by
  have hdvd : p ∣ Nat.card ↥(sigmaCore M) * ((sigmaCore M).subgroupOf M).index := by
    rw [natCard_sigmaCore_mul_index M]; exact hpM
  have h := ((Nat.Prime.dvd_mul hp).1 hdvd).resolve_left hpS
  rwa [index_subgroupOf_left_eq hE] at h

theorem FTS_opposite_sigma_normalizer_beta_support
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₄ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : Statements.FTS_beta_prime_centralizing_sylow.{u})
    (h₆ : Statements.FTS_outside_sigma_plane_structure.{u})
    (h₇ : Statements.FTS_plane_maximal_overgroups.{u})
    (h₈ : Statements.FTS_sigma_prime_separation.{u}) :
    Statements.FTS_opposite_sigma_normalizer_beta_support.{u} := by
  intro G _ _ hG M T Y q hM hT hMT hq hqσ hYM hY hYq hYT hqT p hp hpM hpσT
  have : Fintype G := Fintype.ofFinite G
  have hsimple := hG.isSimpleGroup
  have : Nontrivial G := hG.isSimpleGroup.toNontrivial
  have hG02 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG09 : Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  by_contra hpβT
  have hpβG : p ∉ betaPrimes G := fun h => hpβT <| by
    rw [betaPrimes_subgroup_eq_sigmaPrimes_inter hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hT]
    exact ⟨hpσT, h⟩
  have hnc : ∀ g : G, T ≠ conjSubgroup M g :=
    (FBG_sigma_prime_normalizer_embedding_sylows h₇ G hG02 M T hM hT hMT q hq hqσ Y hYM hY
      hYq hYT).1
  have hsep : sigmaPrimes M ∩ sigmaPrimes T = ∅ :=
    h₈ G hG09 M T hM hT fun g => by rw [conjSub_eq_conjSubgroup]; exact hnc g
  have hpσM : p ∉ sigmaPrimes M := fun h => Set.eq_empty_iff_forall_notMem.1 hsep p ⟨h, hpσT⟩
  obtain ⟨hHallM, -, hderM⟩ := h₁ G hG02 M hM
  obtain ⟨E, -, -, hE⟩ := exists_sigmaComplement hG.not_isMulCommutative hM
    (hG.isSolvable_of_ne_top M hM.1) hHallM hderM
  have hpSM : ¬ p ∣ Nat.card ↥(sigmaCore M) := fun hd =>
    hpσM (isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) p
      (Nat.mem_primeFactors.2 ⟨hp, hd, Nat.card_pos.ne'⟩))
  exact (FBG_sigma_prime_normalizer_outside_narrow_prime_factor h₁ h₂ h₃ h₄ h₅ h₆ h₇ G hG02
    M T hM hT hMT q hq hqσ Y hYM hY hYq hYT E hE p hp
    (dvd_natCard_sigmaComplement hp hE hpM hpSM) hpβG hqT).1 hpσT

end

end CFSG.FeitThompson.Proofs
