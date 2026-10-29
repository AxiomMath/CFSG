module

public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.KappaFreeNonfittingDisplacementSupport
import CFSG.FeitThompson.Local.AbelianAmbientRegularFirstFactorCentral
import CFSG.FeitThompson.Local.NonabelianAmbientSingleRankTwoPrime
import CFSG.FeitThompson.Local.NonabelianAmbientSylowCentralizingKernel
import CFSG.FeitThompson.Local.SigmaComplementThreeHallFactors
import CFSG.FeitThompson.Local.UniqueMaximalOvergroupCentralizerTauOneThree
import CFSG.FeitThompson.Local.TwoBetaFixedCoresHallPosition
import CFSG.FeitThompson.Local.KappaResidualInPrescribedComplement
import CFSG.FeitThompson.Local.NonabelianAmbientPrimeKernelComplement
import CFSG.FeitThompson.Local.TauOneAndDerivedComplementFixedCore
import CFSG.FeitThompson.Local.TauTwoAbelianSylowPropagation
import CFSG.FeitThompson.Local.InvariantRankTwoFactorsFixedFreeCycle
import CFSG.FeitThompson.Local.SinglePrimeOrbitFixedLine
import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
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

theorem FTS_kappa_free_nonfitting_plane_action
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_full_central_hall.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_nonabelian_ambient_unique_nonregular_line.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FPL_low_rank_sylow_central_product.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_kappa_free_nonfitting_plane_action.{u} := by
  intro G _ _ hG q M E Q hc
  have hsimple : IsSimpleGroup G := hG.isSimpleGroup
  have hM : IsCoatom M := hc.isCoatom
  have hEM : E ≤ M := hc.le_of_E
  have hsd := hc.isInternalSemidirectProduct
  have hqp : q.Prime := hc.prime
  have hQE : Q ≤ E := hc.le_of_Q
  have hQcard : Nat.card ↥Q = q := hc.natCard_Q
  have hGosm : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hGfbg : CFSG.FeitThompson.IsFBGAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hsc : _root_.CFSG.FeitThompson.IsSigmaComplement M E := ⟨hM, hsd⟩
  obtain ⟨hqτ₁, hSQ, hDne, -, hDnormM, hDQself, hDQbot, hDS, hτ₂mem⟩ :=
    FTS_kappa_free_nonfitting_displacement_support h₁ h₄ h₆ h₇ h₉ G hG q M E Q hc
  have hDE : (⁅E, Q⁆ : Subgroup G) ≤ E :=
    commutator_le_left_of_le_normalizer (hQE.trans le_normalizer)
  have hDM : (⁅E, Q⁆ : Subgroup G) ≤ M := hDE.trans hEM
  have hMnormD : M ≤ normalizer ((⁅E, Q⁆ : Subgroup G) : Set G) :=
    le_normalizer_of_normal_subgroupOf hDM hDnormM
  have hEnormD : E ≤ normalizer ((⁅E, Q⁆ : Subgroup G) : Set G) := hEM.trans hMnormD
  have hDcard1 : Nat.card ↥(⁅E, Q⁆ : Subgroup G) ≠ 1 := fun h => hDne (Subgroup.card_eq_one.1 h)
  obtain ⟨p, hp, hpD⟩ := Nat.exists_prime_and_dvd hDcard1
  have hpτ₂ : p ∈ tauTwoPrimes M :=
    hτ₂mem p (Nat.mem_primeFactors.2 ⟨hp, hpD, Nat.card_pos.ne'⟩)
  have hpσ : p ∉ sigmaPrimes M := notMem_sigmaPrimes_of_mem_tauTwoPrimes hpτ₂
  have hpq : p ≠ q := by
    intro hpq
    have h1 := elementaryAbelianPRank_eq_one_of_mem_tau1Primes hqτ₁
    have h2 := elementaryAbelianPRank_eq_two_of_mem_tauTwoPrimes hpτ₂
    rw [hpq, h1] at h2
    omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, hAE, hAplane⟩ := exists_plane_le_of_isInternalSemidirectProduct hpτ₂ hsd
  have hAM : A ≤ M := hAE.trans hEM
  have hAcard : Nat.card ↥A = p ^ 2 := hAplane.natCard'
  have hAab : IsMulCommutative ↥A := by
    obtain ⟨e⟩ := hAplane
    exact ⟨⟨fun a b => e.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
  have hosA : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane p M A := ⟨hM, hp, hpσ, hAM, hAplane⟩
  have hEnormA : E ≤ normalizer (A : Set G) := (h₄ G hGosm p M A E hosA hsc hAE).1
  have hnonab : ∃ S : Sylow p G, ¬ IsMulCommutative ↥(S : Subgroup G) := by
    by_contra hcon
    push Not at hcon
    have hEne : E ≠ ⊤ := fun h => hM.1 (top_le_iff.1 (h ▸ hEM))
    haveI hsolvE : Group.IsSolvable ↥E := hG.isSolvable E hEne
    obtain ⟨F₁, F₂, F₃, hsplit, -⟩ := FNI_sigma_complement_three_factors h₁ G hGosm M E hsc
    have hQpi : IsPiSubgroup (tau1Primes M) (Q.subgroupOf E) :=
      isPiSubgroup_subgroupOf_of_natCard_prime hQE hqp hQcard hqτ₁
    obtain ⟨E₁, hE₁E, hQE₁, hE₁hall⟩ := exists_isHallPiSubgroup_tau1_ge (M := M) hQE hQpi
    obtain ⟨c, hcE, hconj⟩ :=
      exists_mem_conj_smul_eq_of_isHallPiSubgroupOf (π := tau1Primes M) hsolvE
        ⟨hsplit.le_E₁, hsplit.isHall_E₁⟩ ⟨hE₁E, hE₁hall⟩
    have hcEself : MulAut.conj c • E = E := conj_smul_eq_self_of_mem hcE
    have hdec : CFSG.FeitThompson.IsTauHallDecomposition
        M E E₁ (MulAut.conj c • F₂) (MulAut.conj c • F₃)
        ((MulAut.conj c • F₂) ⊔ (MulAut.conj c • F₃)) := by
      refine ⟨hE₁E, conj_smul_le_of_le hsplit.le_E₂ ⟨c, hcE⟩,
        conj_smul_le_of_le hsplit.le_E₃ ⟨c, hcE⟩, hE₁hall,
        (isHallPiSubgroupOf_conj_smul ⟨hsplit.le_E₂, hsplit.isHall_E₂⟩ hcE).2,
        (isHallPiSubgroupOf_conj_smul ⟨hsplit.le_E₃, hsplit.isHall_E₃⟩ hcE).2, ?_, ?_, rfl⟩
      · have h := isInternalSemidirectProduct_conj_smul hsplit.outer c
        rwa [hcEself, Subgroup.smul_sup, hconj] at h
      · have h := isInternalSemidirectProduct_conj_smul hsplit.inner c
        rwa [Subgroup.smul_sup, hconj] at h
    obtain ⟨S, hAS⟩ := (IsPGroup.of_card hAcard : IsPGroup p ↥A).exists_le_sylow
    have hAsetup : CFSG.FeitThompson.IsAbelianAmbientSetup
        M p A E (S : Subgroup G) :=
      ⟨hM, hp, hpσ, hAM, hAplane, hEM, hsd, hAE, hcon S, ⟨S, rfl⟩, hAS⟩
    have hQcentre := FBG_abelian_ambient_regular_first_factor_central h₁ h₂ h₄ h₆ h₇ h₉ G hGfbg
      M p A E (S : Subgroup G) E₁ (MulAut.conj c • F₂) (MulAut.conj c • F₃)
      ((MulAut.conj c • F₂) ⊔ (MulAut.conj c • F₃)) hAsetup hdec q hqp Q hQE₁ hQcard hSQ
    rw [centreIn_eq] at hQcentre
    exact hDne (commutator_eq_bot_iff_le_centralizer.2
      (Subgroup.le_centralizer_iff.1 (hQcentre.trans inf_le_right)))
  obtain ⟨Sn, hSn⟩ := hnonab
  have _inst : Fintype G := Fintype.ofFinite G
  have hamb : CFSG.FeitThompson.Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hsetup03 : CFSG.FeitThompson.Prep03.IsPlaneSetup G p M A E :=
    ⟨hamb, hM, hp, hpσ, hAM, isPlane_of_isElementaryAbelianPlane hAplane,
      isSemidirect_of_isInternalSemidirectProduct hsd, hAE⟩
  have hnonab03 : ∃ R : Subgroup G,
      CFSG.FeitThompson.Prep03.IsSylowTop p R ∧
        ¬ IsMulCommutative ↥R :=
    ⟨(Sn : Subgroup G), Sn.card_eq_multiplicity, hSn⟩
  have hτ₂eq : tauTwoPrimes M = {p} :=
    FNI_nonabelian_ambient_single_rank_two_prime h₄ h₆ h₇ h₉ G hamb p M A E hsetup03 hnonab03
  have hnonab4 : ∃ R : Subgroup G,
      _root_.CFSG.FeitThompson.IsSylowSubgroup p R ∧ ¬ IsMulCommutative ↥R :=
    ⟨(Sn : Subgroup G), ⟨Sn, rfl⟩, hSn⟩
  obtain ⟨k, hDcardk⟩ : ∃ k, Nat.card ↥(⁅E, Q⁆ : Subgroup G) = p ^ k := by
    refine ⟨(Nat.card ↥(⁅E, Q⁆ : Subgroup G)).primeFactorsList.length,
      Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_⟩
    intro d hd hdvd
    have hmem := hτ₂mem d (Nat.mem_primeFactors.2 ⟨hd, hdvd, Nat.card_pos.ne'⟩)
    rw [hτ₂eq] at hmem
    simpa using hmem
  have hApgE : IsPGroup p ↥(A.subgroupOf E) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_congr (subgroupOfEquivOfLe hAE).toEquiv, hAcard])
  obtain ⟨S, hAS⟩ := hApgE.exists_le_sylow
  haveI hDnE : ((⁅E, Q⁆ : Subgroup G).subgroupOf E).Normal :=
    normal_subgroupOf_of_le_normalizer hDE hEnormD
  have hDpE : IsPGroup p ↥((⁅E, Q⁆ : Subgroup G).subgroupOf E) :=
    IsPGroup.of_card (by rw [Nat.card_congr (subgroupOfEquivOfLe hDE).toEquiv, hDcardk])
  have hDS' : (⁅E, Q⁆ : Subgroup G).subgroupOf E ≤ (S : Subgroup ↥E) :=
    hDpE.le_sylow_of_normal S
  have hAP : A ≤ (S : Subgroup ↥E).map E.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hAE]
    exact Subgroup.map_mono hAS
  have hDP : (⁅E, Q⁆ : Subgroup G) ≤ (S : Subgroup ↥E).map E.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hDE]
    exact Subgroup.map_mono hDS'
  have hPsyl : _root_.CFSG.FeitThompson.IsSylowIn p E ((S : Subgroup ↥E).map E.subtype) :=
    ⟨S, rfl⟩
  obtain ⟨-, hPcent⟩ :=
    FNI_nonabelian_ambient_sylow_centralizing_kernel h₁ h₃ h₄ h₅ h₆ h₈ G hGosm p M A E hosA hsc
      hAE hnonab4 ((S : Subgroup ↥E).map E.subtype) hPsyl hAP
  obtain ⟨A₀, -, hA₀card, -, -, hA₀eq, -, -⟩ := h₃ G hGosm p M A E hosA hsc hAE hnonab4
  have hA₀cardp :
      Nat.card ↥(A ⊓ centralizer ((sigmaCore M : Subgroup G) : Set G)) = p := by
    rw [← hA₀eq]; exact hA₀card
  have hDcentS : (⁅E, Q⁆ : Subgroup G) ≤ centralizer ((sigmaCore M : Subgroup G) : Set G) :=
    commutator_eq_bot_iff_le_centralizer.1 hDS
  have hDA₀ : (⁅E, Q⁆ : Subgroup G) ≤ A ⊓ centralizer ((sigmaCore M : Subgroup G) : Set G) := by
    rw [← hPcent]; exact le_inf hDP hDcentS
  have hDcardp : Nat.card ↥(⁅E, Q⁆ : Subgroup G) = p := by
    have hdvd : Nat.card ↥(⁅E, Q⁆ : Subgroup G) ∣ p :=
      hA₀cardp ▸ Subgroup.card_dvd_of_le hDA₀
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact absurd h hDcard1
    · exact h
  have hDeq : (⁅E, Q⁆ : Subgroup G) = A ⊓ centralizer ((sigmaCore M : Subgroup G) : Set G) :=
    Subgroup.eq_of_le_of_card_ge hDA₀ (le_of_eq (hA₀cardp.trans hDcardp.symm))
  have hDA : (⁅E, Q⁆ : Subgroup G) ≤ A := le_trans (le_of_eq hDeq) inf_le_left
  have hAQeq : (⁅A, Q⁆ : Subgroup G) = ⁅E, Q⁆ :=
    le_antisymm (Subgroup.commutator_mono hAE le_rfl)
      (by rw [← hDQself]; exact Subgroup.commutator_mono hDA le_rfl)
  have hQnormA : Q ≤ normalizer (A : Set G) := hQE.trans hEnormA
  have hcop : (Nat.card ↥Q).Coprime (Nat.card ↥A) := by
    rw [hQcard, hAcard]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hqp hp).2 (Ne.symm hpq))
  have hsup : (A ⊓ centralizer (Q : Set G)) ⊔ ⁅A, Q⁆ = A :=
    sup_inf_centralizer_commutator_eq_of_le_normalizer hAab hQnormA hcop
  have hinf : (A ⊓ centralizer (Q : Set G)) ⊓ ⁅A, Q⁆ = ⊥ := by
    refine le_antisymm (le_trans ?_ (le_of_eq hDQbot)) bot_le
    rw [hAQeq]
    exact le_inf inf_le_right (le_trans inf_le_left inf_le_right)
  have hnormIn : A ≤ normalizer ((A ⊓ centralizer (Q : Set G) : Subgroup G) : Set G) :=
    le_trans (le_trans (Subgroup.le_centralizer (H := A))
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 inf_le_left)))
      (Subgroup.centralizer_le_normalizer _)
  have hcompl := isComplement'_subgroupOf' (E := A) inf_le_left (hAQeq ▸ hDA) hnormIn hsup hinf
  have hcards := hcompl.card_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_left :
      A ⊓ centralizer (Q : Set G) ≤ A)).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (hAQeq ▸ hDA :
      (⁅A, Q⁆ : Subgroup G) ≤ A)).toEquiv, hAQeq, hDcardp, hAcard] at hcards
  have hCAQ : Nat.card ↥(A ⊓ centralizer (Q : Set G)) = p := by
    have hp0 : 0 < p := hp.pos
    have : Nat.card ↥(A ⊓ centralizer (Q : Set G)) * p = p * p := by
      rw [hcards]; ring
    exact Nat.eq_of_mul_eq_mul_right hp0 this
  exact ⟨p, hp, hpq, hτ₂eq, A, hAE, hAplane, ⟨Sn, hSn⟩, hDeq, hDcardp, hAQeq, hCAQ,
    hAQeq ▸ hDne⟩

end

end CFSG.FeitThompson.Proofs
