module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.OutsideSigmaPlanePrimesTauOneOrTwo
import CFSG.FeitThompson.Local.PlaneNormalizerRankTwoPrimesInSigma
import CFSG.FeitThompson.Local.SigmaTauThreePrimesDerivedContainment
import CFSG.FeitThompson.Local.BetaPrimesSigmaCompatibility
import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.OddOrder.MaximalOvergroupExistence
import CFSG.FeitThompson.OddOrder.FittingSplitsOverHallCore
import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction
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

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

universe u

variable {G : Type*} [Group G]

theorem maximal_isElementaryAbelianSubgroup_subgroupOf {p : ℕ} {A P : Subgroup G} (hAP : A ≤ P)
    (hA : Maximal (IsElementaryAbelianSubgroup p) A) :
    Maximal (IsElementaryAbelianSubgroup p) (A.subgroupOf P) := by
  refine ⟨hA.prop.comap P.subtype_injective, fun B hB hle => ?_⟩
  have hmap : IsElementaryAbelianSubgroup p (B.map P.subtype) := hB.map _
  have hAB : A ≤ B.map P.subtype := fun x hx =>
    ⟨⟨x, hAP hx⟩, hle (show (⟨x, hAP hx⟩ : ↥P) ∈ A.subgroupOf P from hx), rfl⟩
  have h := hA.le_of_ge hmap hAB
  exact fun x hx => h ⟨x, hx, rfl⟩

theorem FTS_kappa_free_nonfitting_plane_transfer
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_hall_abelian.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_kappa_free_nonfitting_plane_transfer.{u} := by
  intro G _ _ hG q M E Q hcfg p A hp _hpq hτ₂ hAE hAplane _hD hDcard hAQ hCAQ
  have := hG.isSimpleGroup
  let _ : Fintype G := Fintype.ofFinite G
  have hfp := Fact.mk hp
  have hG2 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hG4 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hpτ₂ : p ∈ tauTwoPrimes M := by rw [hτ₂]; exact rfl
  obtain ⟨-, hpσM, -⟩ := mem_tauTwoPrimes_iff.1 hpτ₂
  have hAM : A ≤ M := hAE.trans hcfg.le_of_E
  have hplane4 : _root_.CFSG.FeitThompson.IsElementaryAbelianPlane p A := hAplane
  have hOSP : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane p M A :=
    ⟨hcfg.isCoatom, hp, hpσM, hAM, hplane4⟩
  have hSC : _root_.CFSG.FeitThompson.IsSigmaComplement M E :=
    ⟨hcfg.isCoatom, hcfg.isInternalSemidirectProduct⟩
  obtain ⟨hEnormA, -, -, -, -⟩ := h₃ G hG4 p M A E hOSP hSC hAE
  have hAcard : Nat.card ↥A = p ^ 2 := hplane4.natCard'
  have hApg : IsPGroup p ↥A := IsPGroup.of_card hAcard
  have hAne : A ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥A = 1 := Subgroup.card_eq_one.2 h
    rw [hAcard] at h1
    rcases Nat.pow_eq_one.1 h1 with h2 | h2
    · exact hp.one_lt.ne' h2
    · omega
  have hNlt : normalizer (A : Set G) < ⊤ :=
    normalizer_lt_top_of_isPGroup hG.not_isMulCommutative hp hAne hApg
  obtain ⟨T₀, hT₀, hNT₀⟩ := exists_isCoatom_ge_of_ne_top hNlt.ne
  refine ⟨?_, ⟨T₀, hT₀, hNT₀⟩⟩
  intro T hT hNT
  have hTc : IsCoatom T := hT
  have hAT : A ≤ T := le_trans le_normalizer hNT
  have hET : E ≤ T := hEnormA.trans hNT
  have hQT : Q ≤ T := hcfg.le_of_Q.trans hET
  have hpσT : p ∈ sigmaPrimes T :=
    (FNI_plane_normalizer_rank_two_primes_in_sigma h₁ h₂ h₃ h₄ h₅ h₆ G hG4 p M A E T
      hOSP hSC hAE hTc hNT).2 hpτ₂
  have hAST : A ≤ sigmaCore T :=
    le_sigmaCore_of_isPiSubgroup (h₁ G hG2 T hTc).1 hAT (isPiSubgroup_of_plane hp hpσT hplane4)
  have hAmax : Maximal (IsElementaryAbelianSubgroup p) A := (h₅ G hG4 p M A hOSP).2.1
  obtain ⟨P, hAP⟩ := hApg.exists_le_sylow
  have hnarrow : IsPNarrow p ↥(P : Subgroup G) :=
    isPNarrow_of_maximal_card_eq (maximal_isElementaryAbelianSubgroup_subgroupOf hAP hAmax)
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv, hAcard])
  have hpβG : p ∉ betaPrimes G := fun h => not_isPNarrow_of_mem_betaPrimes h P hnarrow
  have hpβT : p ∉ betaPrimes ↥T := fun h =>
    hpβG ((mem_betaPrimes_subgroup_iff_of_mem_sigmaPrimes hpσT).1 h)
  have hDne : (⁅E, Q⁆ : Subgroup G) ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥(⁅E, Q⁆ : Subgroup G) = 1 := Subgroup.card_eq_one.2 h
    rw [hDcard] at h1
    exact hp.one_lt.ne' h1
  have hQnc : ¬ Q ≤ centralizer (A : Set G) := by
    intro hle
    have h0 : (⁅Q, A⁆ : Subgroup G) = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hle
    rw [← Subgroup.commutator_comm, hAQ] at h0
    exact hDne h0
  have hQinf : Q ⊓ centralizer (A : Set G) = ⊥ := by
    have hdvd : Nat.card ↥(Q ⊓ centralizer (A : Set G)) ∣ q := by
      rw [← hcfg.natCard_Q]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases hcfg.prime.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exact Subgroup.card_eq_one.1 h1
    · exact absurd (le_trans (Subgroup.eq_of_le_of_card_ge inf_le_left
        (by rw [hcfg.natCard_Q, h1])).ge inf_le_right) hQnc
  have hqdvd : q ∣ (E ⊓ centralizer (A : Set G)).relIndex E := by
    have hCnormal : ((centralizer (A : Set G)).subgroupOf E).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer
        (hEnormA.trans (normalizer_le_normalizer_centralizer A))
    have hdisj : Disjoint ((centralizer (A : Set G)).subgroupOf E) (Q.subgroupOf E) := by
      rw [Subgroup.disjoint_def]
      intro x hx1 hx2
      have hx : (x : G) ∈ Q ⊓ centralizer (A : Set G) := Subgroup.mem_inf.2 ⟨hx2, hx1⟩
      rw [hQinf] at hx
      exact Subtype.ext (by simpa using hx)
    have h := natCard_dvd_index_of_disjoint _ _ hdisj
    rw [natCard_subgroupOf hcfg.le_of_Q, hcfg.natCard_Q] at h
    rwa [Subgroup.relIndex, Subgroup.inf_subgroupOf_left]
  have hqτ : q ∈ tau1Primes T ∨ q ∈ tauTwoPrimes T :=
    FNI_plane_normalizer_action_prime_transfer h₁ h₂ h₃ h₄ h₅ h₆ G hG4 p M A E T
      hOSP hSC hAE hTc hNT q hcfg.prime hqdvd
  have hST : sigmaCore T ⊓ centralizer (Q : Set G) ≠ ⊥ := by
    intro hbot
    have hle : A ⊓ centralizer (Q : Set G) ≤ ⊥ := hbot ▸ inf_le_inf_right _ hAST
    have h1 : Nat.card ↥(A ⊓ centralizer (Q : Set G)) = 1 :=
      Subgroup.card_eq_one.2 (le_bot_iff.1 hle)
    rw [hCAQ] at h1
    exact hp.one_lt.ne' h1
  exact ⟨hpσT, hpβT, hqτ, hQT, hST⟩

end

end CFSG.FeitThompson.Proofs
