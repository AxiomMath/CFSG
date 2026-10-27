module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.OtherLineNormalizerPlaneProduct
import CFSG.FeitThompson.Local.PlaneMaximalOvergroupUniqueExceptional
import CFSG.FeitThompson.Local.SigmaTauThreePrimesDerivedContainment
import CFSG.FeitThompson.Local.KappaResidualRankTwoExclusion
import CFSG.FeitThompson.Local.SigmaSylowAlphaProductNormal
import CFSG.FeitThompson.Local.AlphaSigmaPrimeSeparation
import CFSG.FeitThompson.Local.NormalImageConfinesCoprimeCommutators
import CFSG.FeitThompson.OddOrder.SigmaPrimesWellDefined
import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction
import CFSG.FeitThompson.Foundations.ProductSubgroupsCardinality
import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
import CFSG.FeitThompson.Definitions.AlphaCore
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson
open Subgroup Pointwise

universe u

variable {G : Type*} [Group G]

theorem coprime_natCard_prime_of_le_sigmaCore [Finite G] {M K : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hKS : K ≤ sigmaCore M) (hpM : p ∉ sigmaPrimes M) : Nat.Coprime (Nat.card ↥K) p :=
  Nat.coprime_comm.1 (hp.coprime_iff_not_dvd.2 fun hdvd =>
    hpM (isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) p
      (Nat.mem_primeFactors.2 ⟨hp, hdvd.trans (Subgroup.card_dvd_of_le hKS), Nat.card_pos.ne'⟩)))

theorem not_conj_of_mem_sigmaPrimes_of_notMem [Finite G] {M T : Subgroup G} {p : ℕ}
    (hpT : p ∈ sigmaPrimes T) (hpM : p ∉ sigmaPrimes M) : ∀ g : G, MulAut.conj g • M ≠ T :=
  fun g hg => hpM (by rw [← sigmaPrimes_conj_smul M g, hg]; exact hpT)

theorem FTS_other_line_normalizer_sigma_centralization
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FPL_low_rank_sylow_central_product.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_other_line_normalizer_sigma_centralization.{u} := by
  intro G _ _ hG M T A A0 p hs hpM
  have : Fintype G := Fintype.ofFinite G
  have hsimple : IsSimpleGroup G := hG.isSimpleGroup
  have hp : p.Prime := hs.prime
  have hfp := Fact.mk hp
  have hM : IsCoatom M := hs.isCoatom_M
  have hT : IsCoatom T := hs.isCoatom_T
  have hAcard : Nat.card ↥A = p ^ 2 := hs.isPlane.natCard
  obtain ⟨hAT, hnorm⟩ :=
    FTS_other_line_normalizer_plane_product h₁ h₂ h₃ h₄ G hG M T A A0 p hs
  set K : Subgroup G := sigmaCore M ⊓ T with hKdef
  have hKS : K ≤ sigmaCore M := inf_le_left
  have hKT : K ≤ T := inf_le_right
  have hAK : A ≤ normalizer ((K : Subgroup G) : Set G) :=
    (le_inf (hs.le.trans (le_normalizer_sigmaCore M)) (hAT.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hKcop : Nat.Coprime (Nat.card ↥K) p :=
    coprime_natCard_prime_of_le_sigmaCore hp hKS hpM
  rw [Subgroup.commutator_comm]
  by_cases hpT : p ∈ sigmaPrimes T
  ·
    have hMin : IsOddOrderMinimalSimple G :=
      ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
    have hMin9 : Prep09.IsMinimalSimpleOddOrder G :=
      ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
    have hAST : A ≤ sigmaCore T :=
      le_sigmaCore_of_isPiSubgroup (h₁ G hMin T hT).1 hAT
        (isPiSubgroup_iff.2 fun r hr => by
          rw [hAcard, Nat.primeFactors_pow _ two_ne_zero, hp.primeFactors,
            Finset.mem_singleton] at hr
          exact hr ▸ hpT)
    have hApg : IsPGroup p ↥(A.subgroupOf (sigmaCore T)) :=
      IsPGroup.of_card (n := 2) (by rw [natCard_subgroupOf hAST]; exact hAcard)
    obtain ⟨Q, hQ⟩ := hApg.exists_le_sylow
    set PT : Subgroup G := (Q : Subgroup ↥(sigmaCore T)).map (sigmaCore T).subtype with hPTdef
    have hAPT : A ≤ PT := by
      have h := Subgroup.map_mono (f := (sigmaCore T).subtype) hQ
      rwa [Subgroup.map_subgroupOf_eq_of_le hAST] at h
    have hPTS : PT ≤ sigmaCore T := Subgroup.map_subtype_le _
    have hPTpg : IsPGroup p ↥PT := Q.isPGroup'.map _
    obtain ⟨hprod, hJnormal⟩ := FTS_sigma_sylow_alpha_product_normal G hMin9 T hT p hpT Q
    set J : Subgroup G := Prep09.alphaCoreIn T ⊔ PT with hJdef
    have hJT : J ≤ T := sup_le (Prep09.alphaCoreIn_le T) (hPTS.trans (sigmaCore_le T))
    have hTJ : T ≤ normalizer ((J : Subgroup G) : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hJT).1 hJnormal
    have hdisj : Disjoint (sigmaPrimes M) (alphaPrimes ↥T) :=
      disjoint_sigmaPrimes_alphaPrimes_of_not_conj hG.not_isMulCommutative hG.odd_natCard
        hG.isSolvable_of_ne_top hM hT
        (not_conj_of_mem_sigmaPrimes_of_notMem hpT hpM)
    have hcard : Nat.card ↥J * Nat.card ↥(Prep09.alphaCoreIn T ⊓ PT)
        = Nat.card ↥(Prep09.alphaCoreIn T) * Nat.card ↥PT := by
      have h := natCard_mul_mul_natCard_inf (Prep09.alphaCoreIn T) PT
      rwa [hprod] at h
    have hJS : J ⊓ sigmaCore M = ⊥ := by
      rw [← Subgroup.card_eq_one]
      by_contra hne
      obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hne
      have hqM : q ∈ sigmaPrimes M :=
        isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) q (Nat.mem_primeFactors.2
          ⟨hq, hqdvd.trans (Subgroup.card_dvd_of_le inf_le_right), Nat.card_pos.ne'⟩)
      have hqmul : q ∣ Nat.card ↥(Prep09.alphaCoreIn T) * Nat.card ↥PT := by
        rw [← hcard]
        exact (hqdvd.trans (Subgroup.card_dvd_of_le inf_le_left)).mul_right _
      rcases (Nat.Prime.dvd_mul hq).1 hqmul with h | h
      · refine Set.disjoint_left.1 hdisj hqM ?_
        refine isPiSubgroup_iff.1
          (isPiSubgroup_map_subtype_iff.2 (isPiSubgroup_alphaCore ↥T)) q ?_
        exact Nat.mem_primeFactors.2 ⟨hq, h, Nat.card_pos.ne'⟩
      · obtain ⟨n, hn⟩ := hPTpg.exists_card_eq
        rw [hn] at h
        exact hpM ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h) ▸ hqM)
    have hKA1 : ⁅K, A⁆ ≤ J := by
      rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono (hAPT.trans le_sup_right) hKT).trans
        (Subgroup.le_normalizer_iff_commutator_le_left.1 hTJ)
    have hKA2 : ⁅K, A⁆ ≤ sigmaCore M :=
      (Subgroup.le_normalizer_iff_commutator_le_left.1 hAK).trans hKS
    exact le_bot_iff.1 ((le_inf hKA1 hKA2).trans hJS.le)
  ·
    have hApgT : IsPGroup p ↥(A.subgroupOf T) :=
      IsPGroup.of_card (n := 2) (by rw [natCard_subgroupOf hAT]; exact hAcard)
    obtain ⟨P, hPT, hPcard, hAP⟩ := exists_sylow_ge_of_isPGroup_subgroupOf hAT hApgT
    have hcfg : IsExceptionalPlaneConfig p T A0 A P :=
      ⟨hT, hp, hpT, hs.le_A, hAP, hPT, hs.natCard_A0,
        nonempty_mulEquiv_of_isPlaneAt hp hs.isPlane, ⟨hPT, hPcard⟩, hs.normalizer_le⟩
    have hamb : IsFTAmbient G :=
      ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
    have hST : sigmaCore T ⊓ sigmaCore M = ⊥ := by
      by_contra hne
      exact hs.ne
        (FTS_exceptional_core_overgroup_uniqueness h₁ h₄ G hamb p T A0 A P hcfg M hM hs.le hne)
    have hDA : (((sigmaCore T).subgroupOf T ⊔ A.subgroupOf T)).Normal := by
      have h := (Subgroup.normal_subgroupOf_iff_le_normalizer
        (sup_le (sigmaCore_le T) hAT)).2 hnorm
      rwa [Subgroup.subgroupOf_sup (sigmaCore_le T) hAT] at h
    have hKn : A.subgroupOf T ≤ normalizer ((K.subgroupOf T : Subgroup ↥T) : Set ↥T) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hKT]
      exact Subgroup.subgroupOf_mono T hAK
    have hcomm := commutator_le_inf_of_sup_normal (D := (sigmaCore T).subgroupOf T)
      hp hApgT hDA (by rw [natCard_subgroupOf hKT]; exact hKcop) hKn
    have hmap : ⁅K, A⁆ ≤ K ⊓ sigmaCore T := by
      have h := Subgroup.map_mono (f := T.subtype) hcomm
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKT,
        Subgroup.map_subgroupOf_eq_of_le hAT] at h
      refine h.trans ((Subgroup.map_inf_le _ _ _).trans ?_)
      rw [Subgroup.map_subgroupOf_eq_of_le hKT,
        Subgroup.map_subgroupOf_eq_of_le (sigmaCore_le T)]
    refine le_bot_iff.1 (hmap.trans ?_)
    rw [← hST]
    exact le_inf inf_le_right (inf_le_left.trans hKS)

end

end CFSG.FeitThompson.Proofs
