module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.AbelianAmbientRegularFirstFactorCentral
import CFSG.FeitThompson.Local.SigmaComplementThreeHallFactors
import CFSG.FeitThompson.Local.OutsideSigmaFixedFreeLineCommutator
import CFSG.FeitThompson.Local.UniqueMaximalOvergroupCentralizerTauOneThree
import CFSG.FeitThompson.Local.TwoBetaFixedCoresHallPosition
import CFSG.FeitThompson.Local.KappaResidualInPrescribedComplement
import CFSG.FeitThompson.Local.TauOneDisplacementReflectedConfiguration
import CFSG.FeitThompson.Local.TauOneAndDerivedComplementFixedCore
import CFSG.FeitThompson.Local.SinglePrimeOrbitFixedLine
import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
import CFSG.FeitThompson.Local.PrimeExtensionMaximalInvariantSubgroup
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

open CFSG.FeitThompson Subgroup Pointwise

universe u

theorem FNI_regular_first_plane_fixed_line_escape
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_full_central_hall.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_nonabelian_ambient_unique_nonregular_line.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_regular_first_plane_fixed_line_escape.{u} := by
  intro G _ _ hG p q M E A Q hsc hp hAE hplane hq hQE hQcard hSQ hAQ
  have hM : IsCoatom M := hsc.isCoatom
  have hEM : E ≤ M := hsc.le
  have hsemi := hsc.isInternalSemidirectProduct
  have hpp : p.Prime := prime_of_mem_tauTwoPrimes hp
  have hpσ : p ∉ sigmaPrimes M := notMem_sigmaPrimes_of_mem_tauTwoPrimes hp
  have hqp : q.Prime := prime_of_mem_tau1Primes hq
  have hqσ : q ∉ sigmaPrimes M := notMem_sigmaPrimes_of_mem_tau1Primes hq
  have hAM : A ≤ M := hAE.trans hEM
  have hosp : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane p M A := ⟨hM, hpp, hpσ, hAM, hplane⟩
  have hGfbg : CFSG.FeitThompson.IsFBGAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG8 : CFSG.FeitThompson.Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hpq : p ≠ q := by
    intro h
    have h2 := elementaryAbelianPRank_eq_two_of_mem_tauTwoPrimes hp
    have h1 := elementaryAbelianPRank_eq_one_of_mem_tau1Primes hq
    rw [h] at h2
    omega
  have hEnormA : E ≤ normalizer (A : Set G) := (h₄ G hG p M A E hosp hsc hAE).1
  have hQnormA : Q ≤ normalizer (A : Set G) := hQE.trans hEnormA
  have hAab : IsMulCommutative ↥A := hplane.isMulCommutative
  have hAcard : Nat.card ↥A = p ^ 2 := hplane.natCard'
  have hApg : IsPGroup p ↥A := hplane.isElementaryAbelianSubgroup.isPGroup
  have hqA : ¬ q ∣ Nat.card ↥A := by
    rw [hAcard]
    intro h
    exact hpq (((Nat.prime_dvd_prime_iff_eq hqp hpp).1 (hqp.dvd_of_dvd_pow h))).symm
  have hcop : (Nat.card ↥Q).Coprime (Nat.card ↥A) := by
    rw [hQcard, hAcard]
    exact Nat.Coprime.pow_right 2 ((Nat.coprime_primes hqp hpp).2 (Ne.symm hpq))
  obtain ⟨hDS, hcyc, -⟩ :=
    FTS_outside_sigma_fixed_free_line_commutator h₁ h₆ h₇ G hG8 M A Q q hM hqp hqσ hAM hAab
      (fun s hs hdvd => by
        rw [hAcard] at hdvd
        rw [(Nat.prime_dvd_prime_iff_eq hs hpp).1 (hs.dvd_of_dvd_pow hdvd)]
        exact hpσ)
      hqA (le_inf hQnormA (hQE.trans hEM)) hQcard hSQ
  set D : Subgroup G := ⁅A, Q⁆ with hDdef
  have hDA : D ≤ A := commutator_le_left_of_le_normalizer hQnormA
  have hDp : Nat.card ↥D = p := by
    have := hcyc
    have hexp : ∀ x : ↥D, x ^ p = 1 := by
      intro x
      have h := hplane.isElementaryAbelianSubgroup.pow_eq_one (x : G) (hDA x.2)
      exact Subtype.ext (by simpa using h)
    have hdvd : Nat.card ↥D ∣ p := by
      rw [← IsCyclic.exponent_eq_card (α := ↥D)]
      exact Monoid.exponent_dvd_of_forall_pow_eq_one hexp
    rcases (Nat.dvd_prime hpp).1 hdvd with h | h
    · exact absurd (Subgroup.card_eq_one.1 h) hAQ
    · exact h
  set X : Subgroup G := A ⊓ centralizer (Q : Set G) with hXdef
  have hXA : X ≤ A := inf_le_left
  have hsup : X ⊔ D = A := sup_inf_centralizer_commutator_eq_of_le_normalizer hAab hQnormA hcop
  have hDXbot : D ⊓ X = ⊥ := by
    refine le_bot_iff.1 (le_trans (le_inf inf_le_left ?_) (le_of_eq
      (inf_centralizer_commutator_eq_bot_of_coprime hQnormA hAab hcop)))
    exact inf_le_right.trans inf_le_right
  have hDcentX : D ≤ centralizer (X : Set G) :=
    hDA.trans ((Subgroup.le_centralizer_iff_isMulCommutative.2 hAab).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hXA)))
  have hcommDX : ⁅D, X⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hDcentX
  have hIDP : IsInternalDirectProduct A D X := by
    refine ⟨hDA, hXA, ?_, hDXbot, hcommDX⟩
    have hDnormX : D ≤ normalizer (X : Set G) :=
      hDcentX.trans (Subgroup.centralizer_le_normalizer _)
    have h := Subgroup.coe_mul_of_left_le_normalizer_right D X hDnormX
    rw [show D ⊔ X = A by rw [sup_comm]; exact hsup] at h
    exact h
  have hXcard : Nat.card ↥X = p := by
    have h := hIDP.card_eq_mul
    rw [hAcard, hDp, pow_two] at h
    exact (Nat.eq_of_mul_eq_mul_left hpp.pos h).symm
  have hnonab : ∃ P : Subgroup G, _root_.CFSG.FeitThompson.IsSylowSubgroup p P ∧
      ¬ IsMulCommutative ↥P := by
    obtain ⟨T, hAT⟩ := hApg.exists_le_sylow
    refine ⟨(T : Subgroup G), ⟨T, rfl⟩, fun hTab => absurd ?_ hAQ⟩
    have hEne : E ≠ ⊤ := fun h => hM.1 (top_le_iff.1 (h ▸ hEM))
    have hEsolv : Group.IsSolvable ↥E := hG.isSolvable_of_ne_top E hEne
    obtain ⟨E₁, E₂, E₃, hspl, -⟩ := FNI_sigma_complement_three_factors h₁ G hG M E hsc
    obtain ⟨F₁, hF₁E, hQF₁, hF₁hall⟩ :=
      exists_isHallPiSubgroup_tau1_ge (M := M) hQE
        (isPiSubgroup_subgroupOf_of_natCard_prime hQE hqp hQcard hq)
    obtain ⟨c, hcE, hconj⟩ :=
      exists_mem_conj_smul_eq_of_isHallPiSubgroupOf hEsolv
        ⟨hspl.le_E₁, hspl.isHall_E₁⟩ ⟨hF₁E, hF₁hall⟩
    have hEconj : MulAut.conj c • E = E :=
      conj_smul_eq_self_iff_mem_normalizer.2 (Subgroup.le_normalizer hcE)
    have hdec : CFSG.FeitThompson.IsTauHallDecomposition
        M E (MulAut.conj c • E₁) (MulAut.conj c • E₂) (MulAut.conj c • E₃)
        ((MulAut.conj c • E₂) ⊔ (MulAut.conj c • E₃)) := by
      refine ⟨Subgroup.conj_smul_le_of_le hspl.le_E₁ ⟨c, hcE⟩,
        Subgroup.conj_smul_le_of_le hspl.le_E₂ ⟨c, hcE⟩,
        Subgroup.conj_smul_le_of_le hspl.le_E₃ ⟨c, hcE⟩,
        (isHallPiSubgroupOf_conj_smul ⟨hspl.le_E₁, hspl.isHall_E₁⟩ hcE).2,
        (isHallPiSubgroupOf_conj_smul ⟨hspl.le_E₂, hspl.isHall_E₂⟩ hcE).2,
        (isHallPiSubgroupOf_conj_smul ⟨hspl.le_E₃, hspl.isHall_E₃⟩ hcE).2, ?_, ?_, rfl⟩
      · have h := isInternalSemidirectProduct_conj_smul hspl.outer c
        rwa [hEconj, Subgroup.smul_sup] at h
      · have h := isInternalSemidirectProduct_conj_smul hspl.inner c
        rwa [Subgroup.smul_sup] at h
    have hAsetup : CFSG.FeitThompson.IsAbelianAmbientSetup
        M p A E (T : Subgroup G) :=
      ⟨hM, hpp, hpσ, hAM, hplane, hEM, hsemi, hAE, hTab, ⟨T, rfl⟩, hAT⟩
    have hQE₁ : Q ≤ MulAut.conj c • E₁ := by rw [hconj]; exact hQF₁
    have hcentral :=
      FBG_abelian_ambient_regular_first_factor_central h₁ h₂ h₄ h₅ h₆ h₇ G hGfbg M p A E
        (T : Subgroup G) (MulAut.conj c • E₁) (MulAut.conj c • E₂) (MulAut.conj c • E₃)
        ((MulAut.conj c • E₂) ⊔ (MulAut.conj c • E₃)) hAsetup hdec q hqp Q hQE₁ hQcard hSQ
    have hQcentE : Q ≤ centralizer (E : Set G) :=
      hcentral.trans (centreIn_le_centralizer E)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2
      (hAE.trans (Subgroup.le_centralizer_iff.1 hQcentE))
  obtain ⟨A₀, -, hA₀card, -, hother, hA₀eq, -, -⟩ :=
    h₃ G hG p M A E hosp hsc hAE hnonab
  have hDA₀ : D = A₀ := by
    refine eq_of_le_of_natCard_eq ?_ (by rw [hA₀card, hDp])
    rw [hA₀eq]
    exact le_inf hDA hDS
  have hXne : X ≠ A₀ := by
    intro h
    have hDX : D = X := hDA₀.trans h.symm
    rw [hDX, inf_idem] at hDXbot
    rw [hDXbot, Subgroup.card_bot] at hXcard
    exact hpp.ne_one hXcard.symm
  refine ⟨hDp, hXcard, hIDP, hDA₀.trans hA₀eq, ?_⟩
  exact (hother X (hXA.trans hAE) hXcard hXne).2

end

end CFSG.FeitThompson.Proofs
