module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.Tau13NoncentralPrimeConfiguration
import CFSG.FeitThompson.Local.TauThreeHallFixedCentralizer
import CFSG.FeitThompson.Local.Tau13CoreFixedSylowRegularNormalizer
import CFSG.FeitThompson.Local.TauOneIntersectionAsymmetry
import CFSG.FeitThompson.Local.NonconjugateIntersectionPrimeCentralization
import CFSG.FeitThompson.Local.SignalizerRegularActionFromBase
import CFSG.FeitThompson.Local.AbelianAmbientNormalHallInertiaExponent
import CFSG.FeitThompson.Local.SigmaComplementExistsNontrivial
import CFSG.FeitThompson.Local.TauTwoFactorContainsPlaneRegularActions
import CFSG.FeitThompson.Local.OvergroupJoinsInvariantPrimeSubgroups
import CFSG.FeitThompson.Local.CentralSylowFixedFreeCycle
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.OddFrobeniusComplementPrimeSubgroupsNormal
import CFSG.FeitThompson.Local.QuotientFittingInvariantComplement
import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.OddOrder.MaximalOvergroupExistence
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson

universe u

variable {G : Type u} [Group G]

theorem le_centralizer_of_le_centralizer_symm {A B : Subgroup G}
    (h : A ≤ centralizer (B : Set G)) : B ≤ centralizer (A : Set G) := by
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer] at h ⊢
  rwa [Subgroup.commutator_comm]

theorem natCard_eq_pow_factorization_of_le_of_le [Finite G] {v : ℕ} (hv : v.Prime)
    {U K S : Subgroup G} (hUK : U ≤ K) (hKS : K ≤ S)
    (hU : Nat.card ↥U = v ^ (Nat.card ↥S).factorization v) :
    Nat.card ↥U = v ^ (Nat.card ↥K).factorization v := by
  have hdvdK : v ^ (Nat.card ↥S).factorization v ∣ Nat.card ↥K :=
    hU ▸ Subgroup.card_dvd_of_le hUK
  have h1 : (Nat.card ↥S).factorization v ≤ (Nat.card ↥K).factorization v :=
    (Nat.Prime.pow_dvd_iff_le_factorization hv Nat.card_pos.ne').1 hdvdK
  have h2 : (Nat.card ↥K).factorization v ≤ (Nat.card ↥S).factorization v :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
      (Subgroup.card_dvd_of_le hKS) v
  rw [hU]
  congr 1
  omega

theorem factorization_natCard_sigmaCore_inf_eq [Finite G] {M L : Subgroup G} {v : ℕ}
    (hv : v.Prime) (hHallG : IsHallPiSubgroup (sigmaPrimes M) (sigmaCore M))
    (hvσ : v ∈ sigmaPrimes M) :
    (Nat.card ↥(sigmaCore M ⊓ L : Subgroup G)).factorization v
      = (Nat.card ↥(M ⊓ L : Subgroup G)).factorization v := by
  have _inst : ((sigmaCore M).subgroupOf M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_sigmaCore M)
  have hJ : sigmaCore M ⊓ (M ⊓ L : Subgroup G) = sigmaCore M ⊓ L := by
    rw [← inf_assoc, inf_eq_left.2 (sigmaCore_le M)]
  have hdvd : (sigmaCore M ⊓ L : Subgroup G).relIndex (M ⊓ L) ∣ (sigmaCore M).index := by
    rw [← hJ]
    exact relIndex_inf_dvd_index (sigmaCore_le M) inf_le_left
  have hnd : ¬ v ∣ (sigmaCore M ⊓ L : Subgroup G).relIndex (M ⊓ L) := fun h =>
    hHallG.notMem_of_mem_primeFactors_index v
      (Nat.mem_primeFactors.2 ⟨hv, h.trans hdvd, Subgroup.index_ne_zero_of_finite⟩) hvσ
  exact factorization_natCard_eq_of_not_dvd_relIndex (le_refl _)
    (le_inf (inf_le_left.trans (sigmaCore_le M)) inf_le_right) hnd

theorem exists_invariant_sylow_le_normalizer [Finite G] {C A : Subgroup G} {v : ℕ} (hv : v.Prime)
    (hsolv : Group.IsSolvable ↥(C ⊔ A)) (hAC : A ≤ normalizer (C : Set G))
    (hcop : (Nat.card ↥C).Coprime (Nat.card ↥A)) :
    ∃ U : Subgroup G, U ≤ C ∧ Nat.card ↥U = v ^ (Nat.card ↥C).factorization v ∧
      A ≤ normalizer (U : Set G) := by
  obtain ⟨U, hUC, hUHall, -, hAU⟩ :=
    exists_isHallSubgroup_subgroupOf_ge_le_normalizer_of_le_normalizer (D := C) (A := A)
      (R := ⊥) hsolv hAC hcop ({v} : Set ℕ) bot_le (by simp [isPiNumber_iff])
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  exact ⟨U, hUC, natCard_eq_pow_factorization_of_isHallSubgroup_singleton hv hUC hUHall, hAU⟩

theorem FNI_tau13_noncentral_third_factor_free
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_prime_normalizer_narrow_rank_bound.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_admissible_tau_one_prime_centralizer_inclusion.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_beta_prime_centralizing_sylow.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_fixed_line_centralizer_unique.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_three_prime_normalizer_transfer.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_tau13_noncentral_third_factor_free.{u} := by
  intro G _ _ hG M E E₁ E₂ E₃ htf p hp P hPE₁ hPcard hPnc
  have _iG : Fintype G := Fintype.ofFinite G
  have := hG.isSimpleGroup
  have hG01 : CFSG.FeitThompson.IsFBGAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG02 : CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG04 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG09 : CFSG.FeitThompson.Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hMc : IsCoatom M := htf.isSigmaComplement.isCoatom
  have hsd := htf.isSigmaComplement.semidirect
  have hEM : E ≤ M := hsd.right_le
  have hE₃E : E₃ ≤ E := htf.le_E₃
  have hE₁E : E₁ ≤ E := htf.le_E₁
  have hPE : P ≤ E := hPE₁.trans hE₁E
  have hPM : P ≤ M := hPE.trans hEM
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_ne_top M hMc.1
  have hsc04 : _root_.CFSG.FeitThompson.IsSigmaComplement M E := ⟨hMc, hsd⟩
  have hsplit04 : _root_.CFSG.FeitThompson.IsNormalizedTauHallSplitting M E E₁ E₂ E₃ :=
    { le_E₁ := htf.le_E₁
      le_E₂ := htf.le_E₂
      le_E₃ := htf.le_E₃
      isHall_E₁ := htf.hall_E₁
      isHall_E₂ := htf.hall_E₂
      isHall_E₃ := htf.hall_E₃
      outer := htf.semidirect_E
      inner := htf.semidirect_E₂₁
      isCyclic_E₁ := htf.isCyclic_E₁
      isCyclic_E₃ := htf.isCyclic_E₃
      le_commutator_E₃ := htf.le_commutator_E₃
      normal_E₂_sup_E₃ := htf.normalizes_E₂E₃
      centralizer_E₃ := htf.centralizer_E₃ }
  obtain ⟨hHallOf, hHallG, -⟩ := h₁ G hG02 M hMc
  have hcop := (isHallOf_and_coprime_of_isInternalSemidirectProduct hHallOf hEM hsd).2
  have hpτ : p ∈ tau1Primes M := by
    obtain ⟨y, hyP, hyp⟩ := exists_mem_orderOf_eq_of_dvd hp (H := P) (by rw [hPcard])
    exact mem_of_isHallPiSubgroup_subgroupOf hE₁E htf.hall_E₁ (hPE₁ hyP) hp hyp
  obtain ⟨q, hq3, Q, hQE₃, hQne, hQcyc, hQsylE₃, hQsylM, hEQ, hQP0, -, hαβ, -, -, -, hAC⟩ :=
    FNI_tau13_noncentral_prime_configuration h₁ h₅ G hG M E E₁ E₂ E₃ htf p hp P hPE₁ hPcard hPnc
  have hQP : Q ⊓ centralizer (P : Set G) = ⊥ := hQP0
  have hq : q.Prime := prime_of_mem_tau3Primes hq3
  have hQM : Q ≤ M := hQsylM.1
  have hQE : Q ≤ E := hQE₃.trans hE₃E
  have hQcard : Nat.card ↥Q = q ^ (Nat.card ↥E₃).factorization q := hQsylE₃.2
  have hQcardM : Nat.card ↥Q = q ^ (Nat.card ↥M).factorization q := hQsylM.2
  have hkne : (Nat.card ↥E₃).factorization q ≠ 0 := by
    intro h
    rw [h, pow_zero] at hQcard
    exact hQne (Subgroup.card_eq_one.1 hQcard)
  have hqQ : q ∣ Nat.card ↥Q := by rw [hQcard]; exact dvd_pow_self q hkne
  obtain ⟨z, hzQ, hzord⟩ := exists_mem_orderOf_eq_of_dvd hq hqQ
  have hZQ : (zpowers z : Subgroup G) ≤ Q := zpowers_le.2 hzQ
  have hZcard : Nat.card ↥(zpowers z : Subgroup G) = q := by rw [Nat.card_zpowers, hzord]
  have hZne : (zpowers z : Subgroup G) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZcard
    exact hq.one_lt.ne hZcard
  have hZpg : IsPGroup q ↥(zpowers z : Subgroup G) := IsPGroup.of_card (by rw [hZcard, pow_one])
  have hZE₃ : (zpowers z : Subgroup G) ≤ E₃ := hZQ.trans hQE₃
  have hZM : (zpowers z : Subgroup G) ≤ M := hZE₃.trans (hE₃E.trans hEM)
  have hNQZ : normalizer (Q : Set G) ≤ normalizer ((zpowers z : Subgroup G) : Set G) := by
    have : ((zpowers z : Subgroup G).subgroupOf Q).Characteristic :=
      @characteristic_of_isCyclic _ _ _ hQcyc _
    have h := normalizer_le_normalizer_map_subtype Q ((zpowers z : Subgroup G).subgroupOf Q)
    rwa [Subgroup.map_subgroupOf_eq_of_le hZQ] at h
  have hNE₃Z : normalizer (E₃ : Set G) ≤ normalizer ((zpowers z : Subgroup G) : Set G) := by
    have : ((zpowers z : Subgroup G).subgroupOf E₃).Characteristic :=
      @characteristic_of_isCyclic _ _ _ htf.isCyclic_E₃ _
    have h := normalizer_le_normalizer_map_subtype E₃ ((zpowers z : Subgroup G).subgroupOf E₃)
    rwa [Subgroup.map_subgroupOf_eq_of_le hZE₃] at h
  have hEZ : E ≤ normalizer ((zpowers z : Subgroup G) : Set G) :=
    htf.semidirect_E.le_normalizer.trans hNE₃Z
  obtain ⟨L, hL, hNZL⟩ := exists_isCoatom_ge_of_ne_top
    (normalizer_lt_top_of_isPGroup hG.not_isMulCommutative hq hZne hZpg).ne
  have hEL : E ≤ L := hEZ.trans hNZL
  have hNQL : normalizer (Q : Set G) ≤ L := hNQZ.trans hNZL
  have hQL : Q ≤ L := Subgroup.le_normalizer.trans hNQL
  have hPL : P ≤ L := hPE.trans hEL
  obtain ⟨hLnc, hXcent, hcomm⟩ :=
    h₈ G hG09 M hMc E hEM hsd q (Or.inr hq3) (zpowers z) hZM hZcard L hL hNZL
  have hQJ : Q ≤ centralizer ((sigmaCore M ⊓ L : Subgroup G) : Set G) := by
    by_cases hb : ⁅(sigmaCore M ⊓ L : Subgroup G), (M ⊓ L : Subgroup G)⁆ = ⊥
    · have h1 : (sigmaCore M ⊓ L : Subgroup G) ≤ centralizer ((M ⊓ L : Subgroup G) : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.1 hb
      exact le_centralizer_of_le_centralizer_symm
        (h1.trans (centralizer_le (SetLike.coe_subset_coe.2 (le_inf hQM hQL))))
    · obtain ⟨hqσL, -⟩ := hcomm hb
      refine hXcent Q (le_inf hQE hQL) ?_
      intro s hs
      rw [hQcard, Nat.primeFactors_prime_pow hkne hq, Finset.mem_singleton] at hs
      exact hs ▸ fun hq1 =>
        (Set.disjoint_left.1 (disjoint_tau1Primes_sigmaPrimes L)) hq1 hqσL
  have hCQ : sigmaCore M ⊓ centralizer (Q : Set G)
      = sigmaCore M ⊓ centralizer (E₃ : Set G) :=
    FNI_tau_three_hall_fixed_centralizer h₈ G hG04 M E E₁ E₂ E₃ hsc04 hsplit04 Q hQE₃ hQne
  have hCJ : sigmaCore M ⊓ centralizer (E₃ : Set G) = sigmaCore M ⊓ L := by
    rw [← hCQ]
    refine le_antisymm (le_inf inf_le_left
      (inf_le_right.trans ((centralizer_le_normalizer _).trans hNQL))) ?_
    exact le_inf inf_le_left (le_centralizer_of_le_centralizer_symm hQJ)
  have hncM : ∀ g : G, L ≠ CFSG.FeitThompson.conjSubgroup M g := hLnc
  have hCbot : sigmaCore M ⊓ centralizer (E₃ : Set G) = ⊥ := by
    by_contra hCne
    obtain ⟨v, hv, hvC⟩ :
        ∃ v, v.Prime ∧ v ∣ Nat.card ↥(sigmaCore M ⊓ centralizer (E₃ : Set G) : Subgroup G) := by
      have h1 : Nat.card ↥(sigmaCore M ⊓ centralizer (E₃ : Set G) : Subgroup G) ≠ 1 := fun h =>
        hCne (Subgroup.card_eq_one.1 h)
      exact ⟨_, Nat.minFac_prime h1, Nat.minFac_dvd _⟩
    have hCS : (sigmaCore M ⊓ centralizer (E₃ : Set G) : Subgroup G) ≤ sigmaCore M := inf_le_left
    have hCM : (sigmaCore M ⊓ centralizer (E₃ : Set G) : Subgroup G) ≤ M :=
      hCS.trans (sigmaCore_le M)
    have hECn : E ≤ normalizer ((sigmaCore M ⊓ centralizer (E₃ : Set G) : Subgroup G) : Set G) :=
      le_normalizer_inf_of_le_normalizer (hEM.trans (le_normalizer_sigmaCore M))
        ((htf.semidirect_E.le_normalizer).trans (normalizer_le_normalizer_centralizer E₃))
    have hsolvCE : Group.IsSolvable
        ↥((sigmaCore M ⊓ centralizer (E₃ : Set G)) ⊔ E : Subgroup G) :=
      isSolvable_of_le_of_isSolvable (sup_le hCM hEM) hMsolv
    have hcopC : (Nat.card ↥(sigmaCore M ⊓ centralizer (E₃ : Set G) : Subgroup G)).Coprime
        (Nat.card ↥E) := Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hCS) hcop
    obtain ⟨U, hUC, hUcard, hEU⟩ := exists_invariant_sylow_le_normalizer hv hsolvCE hECn hcopC
    have hvpos : (Nat.card ↥(sigmaCore M ⊓ centralizer (E₃ : Set G) : Subgroup G)).factorization v
        ≠ 0 := (hv.factorization_pos_of_dvd Nat.card_pos.ne' hvC).ne'
    have hvU : v ∣ Nat.card ↥U := by rw [hUcard]; exact dvd_pow_self v hvpos
    have hUne : U ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hvU
      exact hv.one_lt.ne' (Nat.eq_one_of_dvd_one hvU)
    have hUS : U ≤ sigmaCore M := hUC.trans hCS
    have hUM : U ≤ M := hUC.trans hCM
    have hUJ : U ≤ sigmaCore M ⊓ L := hUC.trans (le_of_eq hCJ)
    have hUL : U ≤ L := hUJ.trans inf_le_right
    obtain ⟨hNUM, hUP⟩ := FNI_tau13_core_fixed_sylow_regular_normalizer h₁ h₆ h₇ h₈ G hG04
      M E E₁ E₂ E₃ hsc04 hsplit04 p q P Q hpτ hPE₁ hPcard hq3
      ((_root_.CFSG.FeitThompson.isSylowIn_iff_natCard hq hQE₃).2 hQcard) hQne hQP hαβ hAC
      L hL (fun g => Ne.symm (hncM g)) hEL hNQL v U hv hvC
      ((_root_.CFSG.FeitThompson.isSylowIn_iff_natCard hv hUC).2 hUcard) hEU
    have hnotcent : ¬ (sigmaCore M ⊓ L : Subgroup G) ≤ centralizer (P : Set G) := by
      intro hle
      exact hUne (le_bot_iff.1 (hUP ▸ le_inf (le_refl U) (hUJ.trans hle)))
    have hJne : ⁅(sigmaCore M ⊓ L : Subgroup G), (M ⊓ L : Subgroup G)⁆ ≠ ⊥ := by
      intro hb
      exact hnotcent ((Subgroup.commutator_eq_bot_iff_le_centralizer.1 hb).trans
        (centralizer_le (SetLike.coe_subset_coe.2 (le_inf hPM hPL))))
    have hsetup : CFSG.FeitThompson.IsNonconjugateSetup M L E p :=
      { isCoatom_M := hMc
        isCoatom_L := hL
        nonconj := hncM
        le_M_E := hEM
        semidirect := hsd
        prime := hp
        dvd_natCard_E := hPcard ▸ Subgroup.card_dvd_of_le hPE
        dvd_natCard_L := hPcard ▸ Subgroup.card_dvd_of_le hPL }
    have hpτL : p ∈ tau1Primes L := by
      by_contra hpn
      have hccc := FBG_nonconjugate_intersection_prime_centralization h₁ h₂ h₃ G hG01 M L E p
        hsetup hpn hJne P (le_inf hPM hPL) (IsPGroup.of_card (n := 1) (by rw [hPcard, pow_one]))
      exact hnotcent (le_centralizer_of_le_centralizer_symm
        (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hccc))
    have hvσ : v ∈ sigmaPrimes M := isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) v
      (Nat.mem_primeFactors.2 ⟨hv, hvU.trans (Subgroup.card_dvd_of_le hUS), Nat.card_pos.ne'⟩)
    have hUsylML : Nat.card ↥U = v ^ (Nat.card ↥(M ⊓ L : Subgroup G)).factorization v := by
      rw [hUcard, hCJ, factorization_natCard_sigmaCore_inf_eq hv hHallG hvσ]
    have hQsylML : Nat.card ↥Q = q ^ (Nat.card ↥(M ⊓ L : Subgroup G)).factorization q :=
      natCard_eq_pow_factorization_of_le_of_le hq (le_inf hQM hQL) inf_le_left hQcardM
    exact FBG_tau_one_intersection_asymmetry h₁ h₄ h₅ h₆ G hG02 M L hMc hL hncM p hp hpτ hpτL
      P (le_inf hPM hPL) hPcard q v hq hv Q U ⟨le_inf hQM hQL, hQsylML⟩
      ⟨le_inf hUM hUL, hUsylML⟩ (le_inf (hPE.trans hEQ) (hPE.trans hEU)) hQP hUP hNQL hNUM
  intro x hx hx1
  rw [CFSG.FeitThompson.Prep05.centralizerIn_eq]
  have hzp : (zpowers x : Subgroup G) ≤ E₃ := zpowers_le.2 hx
  have hne : (zpowers x : Subgroup G) ≠ ⊥ := by
    intro h
    exact hx1 (by simpa [h] using (mem_zpowers x))
  rw [FNI_tau_three_hall_fixed_centralizer h₈ G hG04 M E E₁ E₂ E₃ hsc04 hsplit04
    (zpowers x) hzp hne]
  exact hCbot

end

end CFSG.FeitThompson.Proofs
