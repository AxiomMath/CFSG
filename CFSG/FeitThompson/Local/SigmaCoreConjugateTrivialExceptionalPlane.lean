module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.ExceptionalInvariantSylowSeparation
import CFSG.FeitThompson.Local.SigmaCoreConjugation
import CFSG.FeitThompson.OddOrder.SigmaPrimesWellDefined
import CFSG.FeitThompson.Local.PowerCentralizerTiCriterion
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.MaximalInvariantSubgroupTransport
import CFSG.FeitThompson.Local.OutsideSigmaSylowCentralPrimeElement
import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy
import CFSG.FeitThompson.OddOrder.TypeIIntersectionInSupportingKernel
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

variable {G : Type*} [Group G] [Finite G] {q : ℕ}

theorem le_sigmaCore_of_le_of_isPiSubgroup {N J : Subgroup G}
    (hHall : IsHallPiSubgroup (sigmaPrimes N) ((sigmaCore N).subgroupOf N))
    (hJN : J ≤ N) (hJ : IsPiSubgroup (sigmaPrimes N) J) : J ≤ sigmaCore N := by
  have hcard : Nat.card ↥(J.subgroupOf N) = Nat.card ↥J :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJN).toEquiv
  have hJ' : IsPiSubgroup (sigmaPrimes N) (J.subgroupOf N) :=
    isPiSubgroup_iff.2 fun r hr => isPiSubgroup_iff.1 hJ r (by rwa [hcard] at hr)
  exact le_of_subgroupOf_le hJN (hHall.le_of_isPiSubgroup hJ')

theorem exists_isSylowSubgroupOf_ge_le_normalizer {D A Q : Subgroup G}
    (hsolv : Group.IsSolvable ↥(D ⊔ A)) (hAD : A ≤ normalizer (D : Set G))
    (hcop : (Nat.card ↥D).Coprime (Nat.card ↥A)) (hq : q.Prime)
    (hQD : Q ≤ D) (hAQ : A ≤ normalizer (Q : Set G)) (hQq : IsPGroup q ↥Q) :
    ∃ S : Subgroup G, IsSylowSubgroupOf q S D ∧ Q ≤ S ∧ A ≤ normalizer (S : Set G) := by
  have := Fact.mk hq
  obtain ⟨S, hSD, hSq, hQS, hAS, hidx⟩ :=
    exists_isPGroup_ge_le_normalizer_not_dvd_index hsolv hAD hcop hq hQD hAQ hQq
  refine ⟨S, ⟨hSD, ?_⟩, hQS, hAS⟩
  have hcard : Nat.card ↥(Subgroup.comap D.subtype S) = Nat.card ↥S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSD).toEquiv
  have h := natCard_eq_pow_factorization_iff.2
    ⟨hSq.comap_of_injective _ D.subtype_injective, hidx⟩
  rwa [hcard] at h

theorem FTS_exceptional_core_conjugate_intersection
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FTS_exceptional_core_conjugate_intersection.{u} := by
  intro G _ _ hG p M A₀ A P hc g hgM hAMg
  have hsep := FTS_exceptional_invariant_sylow_separation h₁ h₂ G hG p M A₀ A P hc
  have : Fintype G := Fintype.ofFinite G
  have hMin : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hconj : ∀ (Y : Subgroup G) (c : G), conjBy Y c = MulAut.conj c⁻¹ • Y := fun _ _ => rfl
  have hp : p.Prime := hc.prime
  have hM : IsCoatom M := hc.isCoatom
  have hAM : A ≤ M := hc.le_of_A.trans hc.le_of_P
  have hAcard : Nat.card ↥A = p ^ 2 := hc.isElementaryAbelianPlane.natCard hp.ne_zero
  set N : Subgroup G := conjBy M g with hNdef
  have hN : IsCoatom N := by
    rw [hNdef, hconj, conj_smul_eq_map_conj]
    exact isCoatom_map_conj hM g⁻¹
  have hσN : sigmaPrimes N = sigmaPrimes M := by
    rw [hNdef, hconj]; exact sigmaPrimes_conj_smul M g⁻¹
  have hSN : sigmaCore N = conjBy (sigmaCore M) g := by
    rw [hNdef, hconj, hconj, sigmaCore_conj_smul]
  obtain ⟨-, hHallN⟩ := (h₁ G hMin N hN).1
  have hsolvM : ∀ X : Subgroup G, X ≤ M → Group.IsSolvable ↥X := fun X hX =>
    hG.isSolvable X fun h => hM.1 (top_le_iff.1 (h ▸ hX))
  have hsolvN : ∀ X : Subgroup G, X ≤ N → Group.IsSolvable ↥X := fun X hX =>
    hG.isSolvable X fun h => hN.1 (top_le_iff.1 (h ▸ hX))
  have hcop : ∀ D : Subgroup G, ¬ p ∣ Nat.card ↥D → (Nat.card ↥D).Coprime (Nat.card ↥A) := by
    intro D h
    rw [hAcard]
    exact Nat.Coprime.pow_right 2 ((hp.coprime_iff_not_dvd).2 h).symm
  have hpSM : ¬ p ∣ Nat.card ↥(sigmaCore M) := fun hdvd =>
    hc.notMem_sigmaPrimes (isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) p
      (Nat.mem_primeFactors.2 ⟨hp, hdvd, Nat.card_pos.ne'⟩))
  have hpSN : ¬ p ∣ Nat.card ↥(sigmaCore N) := fun hdvd =>
    hc.notMem_sigmaPrimes (hσN ▸ isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore N) p
      (Nat.mem_primeFactors.2 ⟨hp, hdvd, Nat.card_pos.ne'⟩))
  have hASM : A ≤ normalizer ((sigmaCore M : Subgroup G) : Set G) :=
    hAM.trans (le_normalizer_sigmaCore M)
  have hASN : A ≤ normalizer ((sigmaCore N : Subgroup G) : Set G) :=
    hAMg.trans (le_normalizer_sigmaCore N)
  set J : Subgroup G := sigmaCore M ⊓ N with hJdef
  have hJSM : J ≤ sigmaCore M := inf_le_left
  have hJN : J ≤ N := inf_le_right
  have hJSN : J ≤ sigmaCore N :=
    le_sigmaCore_of_le_of_isPiSubgroup hHallN hJN
      (by rw [hσN]; exact (isPiSubgroup_sigmaCore M).of_le hJSM)
  have hAJ : A ≤ normalizer ((J : Subgroup G) : Set G) :=
    le_trans (le_inf hASM (hAMg.trans Subgroup.le_normalizer))
      Subgroup.inf_normalizer_le_normalizer_inf
  have hpJ : ¬ p ∣ Nat.card ↥J := fun hdvd =>
    hpSM (hdvd.trans (Subgroup.card_dvd_of_le hJSM))
  have hJbot : J = ⊥ := by
    by_contra hJne
    obtain ⟨q, hq, hqJ⟩ := Nat.exists_prime_and_dvd fun h => hJne (Subgroup.card_eq_one.1 h)
    have hqσ : q ∈ sigmaPrimes M :=
      isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) q (Nat.mem_primeFactors.2
        ⟨hq, hqJ.trans (Subgroup.card_dvd_of_le hJSM), Nat.card_pos.ne'⟩)
    have hAbotn : A ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
      rw [Subgroup.normalizer_eq_top]; exact le_top
    obtain ⟨Q₀, hQ₀, -, hAQ₀⟩ := exists_isSylowSubgroupOf_ge_le_normalizer
      (Q := (⊥ : Subgroup G))
      (hsolvM _ (sup_le (hJSM.trans (sigmaCore_le M)) hAM)) hAJ (hcop J hpJ) hq bot_le
      hAbotn IsPGroup.of_bot
    have hQ₀q : IsPGroup q ↥Q₀ := IsPGroup.of_card hQ₀.2
    have hQ₀ne : Q₀ ≠ ⊥ := by
      intro h
      have hpos : 0 < (Nat.card ↥J).factorization q :=
        hq.factorization_pos_of_dvd Nat.card_pos.ne' hqJ
      have h2 := hQ₀.2
      rw [h, Subgroup.card_bot] at h2
      exact absurd h2.symm (Nat.one_lt_pow hpos.ne' hq.one_lt).ne'
    obtain ⟨Q₁, hQ₁, hQ₀Q₁, hAQ₁⟩ := exists_isSylowSubgroupOf_ge_le_normalizer
      (hsolvM _ (sup_le (sigmaCore_le M) hAM)) hASM (hcop _ hpSM) hq
      (hQ₀.1.trans hJSM) hAQ₀ hQ₀q
    obtain ⟨Q₂, hQ₂, hQ₀Q₂, hAQ₂⟩ := exists_isSylowSubgroupOf_ge_le_normalizer
      (hsolvN _ (sup_le (sigmaCore_le N) hAMg)) hASN (hcop _ hpSN) hq
      (hQ₀.1.trans hJSN) hAQ₀ hQ₀q
    have hQ₂' : IsSylowSubgroupOf q Q₂ (conjBy (sigmaCore M) g) := by rw [← hSN]; exact hQ₂
    obtain ⟨hinf, -⟩ := hsep q hqσ g hgM hAMg Q₁ Q₂ hQ₁ hQ₂' hAQ₁ hAQ₂
    exact hQ₀ne (le_bot_iff.1 (hinf ▸ le_inf hQ₀Q₁ hQ₀Q₂))
  refine ⟨hJbot, ?_⟩
  have hCA₀ : centralizer ((conjBy A₀ g : Subgroup G) : Set G) ≤ N := by
    have h1 : centralizer ((conjBy A₀ g : Subgroup G) : Set G)
        = conjBy (centralizer (A₀ : Set G)) g := by
      rw [hconj, hconj, ← smul_centralizer_coe]
    rw [h1, hNdef]
    exact conjBy_le_conjBy_iff.2 ((centralizer_le_normalizer _).trans hc.normalizer_le)
  exact le_bot_iff.1 (hJbot ▸ le_inf inf_le_left (inf_le_right.trans hCA₀))

end

end CFSG.FeitThompson.Proofs
