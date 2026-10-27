module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
import CFSG.FeitThompson.Local.NonTIFittingNilpotentCoreBetaExclusion
import CFSG.FeitThompson.Local.SigmaComplementThreeHallFactors
import CFSG.FeitThompson.Local.CommonPrimeFixedCoreFittingEnvelope
import CFSG.FeitThompson.Local.FiveTypeLocalClassification
import CFSG.FeitThompson.Local.KappaResidualInPrescribedComplement
import CFSG.FeitThompson.Local.SplitPrimeKernelFreeComplement
import CFSG.FeitThompson.Local.MixedFittingCentralizerConstrained
import CFSG.FeitThompson.Local.InvariantRankTwoFactorsFixedFreeCycle
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise _root_.CFSG.FeitThompson

universe u

variable {G : Type u} [Group G] {M E : Subgroup G} {g : G} {p : ℕ}

theorem eq_bot_of_isHallPiSubgroup_empty [Finite G] {A : Subgroup G} (hle : A ≤ E)
    (hHall : IsHallPiSubgroup (∅ : Set ℕ) (A.subgroupOf E)) : A = ⊥ := by
  have hcard : Nat.card ↥(A.subgroupOf E) = 1 := by
    have hempty : (Nat.card ↥(A.subgroupOf E)).primeFactors = ∅ := by
      ext q
      simp only [Finset.notMem_empty, iff_false]
      intro hq
      exact isPiSubgroup_iff.1 hHall.isPiSubgroup q hq
    rcases Nat.primeFactors_eq_empty.1 hempty with h | h
    · exact absurd h Nat.card_pos.ne'
    · exact h
  rw [natCard_subgroupOf_eq hle] at hcard
  exact Subgroup.card_eq_one.1 hcard

theorem disjoint_tauTwoPrimes_tau1Primes (M : Subgroup G) :
    Disjoint (tauTwoPrimes M) (tau1Primes M) :=
  Set.disjoint_left.2 fun _ h h' => by
    have h2 := elementaryAbelianPRank_eq_two_of_mem_tauTwoPrimes h
    have h1 := elementaryAbelianPRank_eq_one_of_mem_tau1Primes h'
    omega

section SylowProduct

variable [Finite G]

noncomputable def sylowSubgroupIn (X : Subgroup G) (p : ℕ) : Subgroup G :=
  if h : p.Prime then
    have := Fact.mk h
    ((Classical.arbitrary (Sylow p ↥X) : Subgroup ↥X)).map X.subtype
  else ⊥

theorem sylowSubgroupIn_of_not_prime (X : Subgroup G) (hp : ¬ p.Prime) :
    sylowSubgroupIn X p = ⊥ := by
  rw [sylowSubgroupIn, dif_neg hp]

theorem isSylowSubgroupIn_sylowSubgroupIn (X : Subgroup G) (hp : p.Prime) :
    IsSylowSubgroupIn (sylowSubgroupIn X p) X p := by
  have := Fact.mk hp
  refine ⟨?_, ?_⟩
  · rw [sylowSubgroupIn, dif_pos hp]
    exact Subgroup.map_subtype_le _
  · rw [sylowSubgroupIn, dif_pos hp, Subgroup.card_map_of_injective X.subtype_injective]
    exact Sylow.card_eq_multiplicity _

theorem sylowSubgroupIn_le (X : Subgroup G) (p : ℕ) : sylowSubgroupIn X p ≤ X := by
  by_cases hp : p.Prime
  · exact (isSylowSubgroupIn_sylowSubgroupIn X hp).1
  · rw [sylowSubgroupIn_of_not_prime X hp]
    exact bot_le

theorem natCard_sylowSubgroupIn (X : Subgroup G) (hp : p.Prime) :
    Nat.card ↥(sylowSubgroupIn X p) = p ^ (Nat.card ↥X).factorization p :=
  (isSylowSubgroupIn_sylowSubgroupIn X hp).2

noncomputable def sylowProductOutsideSigma (M : Subgroup G) : Subgroup G :=
  ⨆ p ∈ {p ∈ {p : ℕ | p.Prime ∧ p ∉ sigmaPrimes M} | p ∣ Nat.card ↥(mixedFitting M)},
    sylowSubgroupIn (mixedFitting M) p

theorem isSylowProduct_sylowProductOutsideSigma (M : Subgroup G) :
    IsSylowProduct (sylowProductOutsideSigma M) (mixedFitting M)
      {p : ℕ | p.Prime ∧ p ∉ sigmaPrimes M} :=
  ⟨sylowSubgroupIn (mixedFitting M),
    fun _ hp _ => isSylowSubgroupIn_sylowSubgroupIn (mixedFitting M) hp.1, rfl⟩

theorem sylowProductOutsideSigma_le (M : Subgroup G) :
    sylowProductOutsideSigma M ≤ mixedFitting M := by
  rw [sylowProductOutsideSigma]
  exact iSup₂_le fun p _ => sylowSubgroupIn_le _ p

theorem sylowSubgroupIn_le_sylowProductOutsideSigma {M : Subgroup G} (hp : p.Prime)
    (hpσ : p ∉ sigmaPrimes M) (hpd : p ∣ Nat.card ↥(mixedFitting M)) :
    sylowSubgroupIn (mixedFitting M) p ≤ sylowProductOutsideSigma M :=
  le_biSup (f := fun q => sylowSubgroupIn (mixedFitting M) q) ⟨⟨hp, hpσ⟩, hpd⟩

end SylowProduct

theorem tau3Primes_eq_empty_of_inf_conj_mixedFitting_ne_bot [Finite G]
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_nilpotent_sigma_core_fitting_structure.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_nonnilpotent_sigma_core_hall_structure.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    (hG : IsFBGAmbient G) (hM : IsCoatom M) (hg : g ∉ M)
    (hne : mixedFitting M ⊓ conjSubgroup (mixedFitting M) g ≠ ⊥) :
    tau3Primes M = ∅ := by
  obtain ⟨-, -, -, -, hM'F, hprod, -, hYτ⟩ :=
    _root_.CFSG.FeitThompson.Proofs.FBG_nonti_fitting_nilpotent_core_and_beta_exclusion h₁ h₂ h₃ h₄
      G hG M _ g ⟨hM, hg, rfl, hne⟩ _ (isSylowProduct_sylowProductOutsideSigma M)
  refine Set.eq_empty_iff_forall_notMem.2 fun p hp => ?_
  have hpp : p.Prime := prime_of_mem_tau3Primes hp
  have hpσ : p ∉ sigmaPrimes M := notMem_sigmaPrimes_of_mem_tau3Primes hp
  have hpF : p ∣ Nat.card ↥(mixedFitting M) :=
    (dvd_natCard_commutator_of_mem_tau3Primes hp).trans (Subgroup.card_dvd_of_le hM'F)
  have hpS : ¬ p ∣ Nat.card ↥(sigmaCore M) := fun hd =>
    hpσ (isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) p
      (Nat.mem_primeFactors.2 ⟨hpp, hd, Nat.card_pos.ne'⟩))
  rw [hprod.card_eq_mul] at hpF
  have hpY : p ∣ Nat.card ↥(sylowProductOutsideSigma M) :=
    ((Nat.Prime.dvd_mul hpp).1 hpF).resolve_left hpS
  have hpτ₂ : p ∈ tauTwoPrimes M := hYτ (Nat.mem_primeFactors.2 ⟨hpp, hpY, Nat.card_pos.ne'⟩)
  have h1 : elementaryAbelianPRank p ↥M = 1 := elementaryAbelianPRank_eq_one_of_mem_tau3Primes hp
  have h2 : elementaryAbelianPRank p ↥M = 2 :=
    elementaryAbelianPRank_eq_two_of_mem_tauTwoPrimes hpτ₂
  omega

theorem sigmaComplement_tau_hall_structure [Finite G]
    (h₃ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (hG : IsFBGAmbient G) (hM : IsCoatom M) (hτ₃ : tau3Primes M = ∅)
    (hsd : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E) :
    (∀ E₂ : Subgroup G, E₂ ≤ E → IsHallPiSubgroup (tauTwoPrimes M) (E₂.subgroupOf E) →
        (E₂.subgroupOf E).Normal ∧ IsCyclicQuotient E E₂ ∧
          ∀ E₁ : Subgroup G, E₁ ≤ E → IsHallPiSubgroup (tau1Primes M) (E₁.subgroupOf E) →
            FreeCore.IsInternalSemidirectProduct E E₂ E₁ ∧ IsQuotientMulEquivTo E E₂ E₁) ∧
      (tauTwoPrimes M = ∅ → IsCyclic ↥E) ∧
      (∀ E₃ : Subgroup G, E₃ ≤ E → IsHallPiSubgroup (tau3Primes M) (E₃.subgroupOf E) →
        E₃ = ⊥) := by
  have hG2 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  obtain ⟨E₁s, E₂s, E₃s, hsplit, -⟩ :=
    _root_.CFSG.FeitThompson.Proofs.FNI_sigma_complement_three_factors h₃ G hG2 M E ⟨hM, hsd⟩
  have hE₃s : E₃s = ⊥ :=
    eq_bot_of_isHallPiSubgroup_empty hsplit.le_E₃ (hτ₃ ▸ hsplit.isHall_E₃)
  have hsup : E₂s ⊔ E₁s = E := by
    have h := hsplit.outer.sup_eq
    rwa [hE₃s, bot_sup_eq] at h
  have hinner : FreeCore.IsInternalSemidirectProduct E E₂s E₁s := hsup ▸ hsplit.inner
  have hnormal : (E₂s.subgroupOf E).Normal := hinner.normal_subgroupOf
  refine ⟨fun E₂ hE₂ hE₂Hall => ?_, fun hτ₂ => ?_, fun E₃ hE₃ hE₃Hall =>
    eq_bot_of_isHallPiSubgroup_empty hE₃ (hτ₃ ▸ hE₃Hall)⟩
  ·
    have hEeq : E₂ = E₂s := by
      refine eq_of_subgroupOf_eq hE₂ hsplit.le_E₂ (Subgroup.eq_of_le_of_card_ge ?_ ?_)
      · exact hsplit.isHall_E₂.le_of_isPiSubgroup hE₂Hall.isPiSubgroup
      · exact le_of_eq
          (CFSG.FeitThompson.Proofs.natCard_eq_of_isHallPiSubgroup hsplit.isHall_E₂ hE₂Hall)
    subst hEeq
    refine ⟨hnormal, ⟨hnormal, ?_⟩, fun E₁ hE₁ hE₁Hall => ?_⟩
    · exact (((isComplement'_subgroupOf_of_isInternalSemidirectProduct
        hinner).symm.QuotientMulEquiv.trans
          (Subgroup.subgroupOfEquivOfLe hsplit.le_E₁)).isCyclic).2 hsplit.isCyclic_E₁
    ·
      have hcard₁ : Nat.card ↥(E₁.subgroupOf E) = Nat.card ↥E₁s := by
        rw [CFSG.FeitThompson.Proofs.natCard_eq_of_isHallPiSubgroup hE₁Hall hsplit.isHall_E₁,
          natCard_subgroupOf_eq hsplit.le_E₁]
      have hprod : Nat.card ↥(E₂.subgroupOf E) * Nat.card ↥(E₁.subgroupOf E) = Nat.card ↥E := by
        rw [natCard_subgroupOf_eq hE₂, hcard₁, hinner.natCard_eq_mul]
      have hcop : (Nat.card ↥(E₂.subgroupOf E)).Coprime (Nat.card ↥(E₁.subgroupOf E)) :=
        coprime_natCard_of_isPiSubgroup (disjoint_tauTwoPrimes_tau1Primes M)
          hE₂Hall.isPiSubgroup hE₁Hall.isPiSubgroup
      have hcompl : (E₂.subgroupOf E).IsComplement' (E₁.subgroupOf E) :=
        Subgroup.isComplement'_of_coprime hprod hcop
      refine ⟨⟨?_, le_normalizer_of_normal_subgroupOf hE₂ hnormal, ?_⟩, hnormal,
        ⟨hcompl.symm.QuotientMulEquiv.trans (Subgroup.subgroupOfEquivOfLe hE₁)⟩⟩
      · have h := congrArg (Subgroup.map E.subtype) hcompl.sup_eq_top
        rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hE₂,
          Subgroup.map_subgroupOf_eq_of_le hE₁, _root_.CFSG.FeitThompson.Proofs.map_subtype_top] at h
      · exact _root_.CFSG.FeitThompson.Proofs.disjoint_of_disjoint_subgroupOf hE₂ hcompl.disjoint
  ·
    have hE₂s : E₂s = ⊥ :=
      eq_bot_of_isHallPiSubgroup_empty hsplit.le_E₂ (hτ₂ ▸ hsplit.isHall_E₂)
    rw [hE₂s, bot_sup_eq] at hsup
    exact hsup ▸ hsplit.isCyclic_E₁

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open CFSG.FeitThompson Subgroup

universe u

theorem FBG_nonti_fitting_cyclic_complement
    (h₁ : Statements.FBG_nilpotent_sigma_core_fitting_structure.{u})
    (h₂ : Statements.FBG_nonnilpotent_sigma_core_hall_structure.{u})
    (h₃ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₄ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FBG_nonti_fitting_cyclic_complement.{u} := by
  intro G _ _ hG M g hM hg hne
  have hτ₃ : tau3Primes M = ∅ :=
    tau3Primes_eq_empty_of_inf_conj_mixedFitting_ne_bot h₁ h₂ h₃ h₄ hG hM hg hne
  exact ⟨hτ₃, fun E _ hsd => sigmaComplement_tau_hall_structure h₃ hG hM hτ₃ hsd⟩

end

end CFSG.FeitThompson.Proofs
