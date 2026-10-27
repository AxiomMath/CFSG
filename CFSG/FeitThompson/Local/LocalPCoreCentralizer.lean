module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.KappaFixedSubgroupDerivedAndHall
import CFSG.FeitThompson.Local.KappaDerivedComplement
import CFSG.FeitThompson.Local.ExceptionalPrimeFixedConfiguration
import CFSG.FeitThompson.Local.OutsideSigmaDerivedCentralizerCyclic
import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
import CFSG.FeitThompson.Local.CyclicCentralizerFactorRestriction
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.BetaSylowNormalizerUniqueMaximal
import CFSG.FeitThompson.Local.PrimeFixedMinimalQuotient
import CFSG.FeitThompson.Definitions.NormalSylowHallCore
import CFSG.FeitThompson.Definitions.NarrowPGroupsAndBetaPrimes
import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
import CFSG.FeitThompson.Definitions.TauTwoPrimes
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G]

theorem exists_isSylowProduct_of_forall_prime [Finite G] (X : Subgroup G) (π : Set ℕ)
    (hπ : ∀ p ∈ π, p.Prime) : ∃ Y : Subgroup G, CFSG.FeitThompson.IsSylowProduct Y X π := by
  classical
  have hex : ∀ p : ℕ, ∃ R : Subgroup G,
      p.Prime → CFSG.FeitThompson.IsSylowSubgroupIn R X p := by
    intro p
    by_cases hp : p.Prime
    · have := Fact.mk hp
      obtain ⟨P⟩ : Nonempty (Sylow p ↥X) := inferInstance
      refine ⟨(P : Subgroup ↥X).map X.subtype, fun _ => ⟨Subgroup.map_subtype_le _, ?_⟩⟩
      rw [Subgroup.card_map_of_injective X.subtype_injective, P.card_eq_multiplicity]
    · exact ⟨⊥, fun h => absurd h hp⟩
  choose Q hQ using hex
  exact ⟨_, Q, fun p hp _ => hQ p (hπ p hp), rfl⟩

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup Pointwise CFSG.FeitThompson
open CFSG.FeitThompson

universe u

theorem FBG_local_p_core_centralizer
    (h₁ : Statements.FBG_nilpotent_sigma_core_fitting_structure.{u})
    (h₂ : Statements.FBG_nonnilpotent_sigma_core_hall_structure.{u})
    (h₃ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₄ : Statements.FNI_kappa_local_pair.{u})
    (h₅ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₆ : Statements.FNI_kappa_trivial_residual_prime_fixed_core.{u})
    (_h₇ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (_h₈ : Statements.FTS_outside_sigma_plane_structure.{u}) :
    Statements.FBG_local_p_core_centralizer.{u} := by
  intro G _ _ hG M K U hsetup hKbot
  have : Fintype G := Fintype.ofFinite G
  have hM := hsetup.isCoatom
  have hKM := hsetup.le_M_K
  have hKhall := hsetup.hall_K
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable M hM.1
  have hamb : Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hGmin : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  obtain ⟨hAne, hAcyc, hAle, hcentM'⟩ :=
    FBG_kappa_fixed_subgroup_derived_and_hall h₂ h₄ h₅ h₆ G hG M K hM hKbot hKM hKhall
  have hHall : Prep03.IsHallPiOf (kappaPrimes M) K M :=
    isHallPiOf_of_isHallPiSubgroup_subgroupOf hKM hKhall
  have hκ : (kappaPrimes M).Nonempty := by
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := Nat.card ↥K)
      (fun h => hKbot (Subgroup.card_eq_one.1 h))
    exact ⟨p, hHall.2.1 p (Nat.mem_primeFactors.2 ⟨hp, hpd, Nat.card_pos.ne'⟩)⟩
  set A : Subgroup G := centralizerWithin (sigmaCore M) K with hAdef
  have hsetupκ : Prep03.IsKappaSetup G M K A (K ⊔ A) :=
    { ambient := hamb, isCoatom := hM, kappa_nonempty := hκ, isHall_K := hHall,
      A_eq := rfl, Z_eq := rfl }
  obtain ⟨-, -, hM'eq⟩ := FNI_kappa_derived_complement h₄ h₅ G M K A _ hsetupκ
  have hM'sup : (⁅M, M⁆ : Subgroup G) = sigmaCore M ⊔ U :=
    hM'eq U (isSemidirect_of_isInternalSemidirectProduct hsetup.semidirect_M)
      (isSemidirect_of_isInternalSemidirectProduct hsetup.semidirect_UK)
  have hM'set : ((⁅M, M⁆ : Subgroup G) : Set G) = (sigmaCore M : Set G) * (U : Set G) := by
    rw [hM'sup]
    exact Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (hsetup.le_M_U.trans hsetup.semidirect_M.le_normalizer)
  have hM'M : (⁅M, M⁆ : Subgroup G) ≤ M :=
    Subgroup.commutator_le.2 fun x hx y hy => by
      rw [commutatorElement_def]
      exact M.mul_mem (M.mul_mem (M.mul_mem hx hy) (M.inv_mem hx)) (M.inv_mem hy)
  have hnotcyc : ¬ IsCyclic ↥(hallCoreIn M) := by
    intro hcyc
    by_cases hnil : Group.IsNilpotent ↥(sigmaCore M)
    ·
      obtain ⟨Y, hY⟩ := exists_isSylowProduct_of_forall_prime (mixedFitting M)
        {p : ℕ | p.Prime ∧ p ∉ sigmaPrimes M} (fun _ hp => hp.1)
      obtain ⟨hHS, -, hYcyc, hYτ, hdp, -, -, -, -⟩ := h₁ G hG M hM hnil Y hY
      have hScyc : IsCyclic ↥(sigmaCore M) := hHS ▸ hcyc
      have hcop : (Nat.card ↥(sigmaCore M)).Coprime (Nat.card ↥Y) :=
        coprime_natCard_of_primeFactors_disjoint
          (fun r hr => isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) r hr)
          (fun r hr => hYτ (Finset.mem_coe.2 hr))
          (fun r hrσ hrτ => (mem_tauTwoPrimes_iff.1 hrτ).2.1 hrσ)
      have : IsCyclic (↥(sigmaCore M) × ↥Y) := Group.isCyclic_prod_iff.2 ⟨hScyc, hYcyc, hcop⟩
      have hFcyc : IsCyclic ↥(mixedFitting M) := isCyclic_of_mulEquiv hdp.mulEquivProd
      have hM'cent : (⁅M, M⁆ : Subgroup G) ≤
          centralizer ((mixedFitting M : Subgroup G) : Set G) :=
        commutator_le_centralizer_of_isCyclic (le_normalizer_mixedFitting M)
      have hM'F : (⁅M, M⁆ : Subgroup G) ≤ mixedFitting M := by
        rw [mixedFitting_eq] at hM'cent ⊢
        exact le_map_fittingRaw_of_le_centralizer hM'M hM'cent
      have hM'cyc : IsCyclic ↥(⁅M, M⁆ : Subgroup G) := Subgroup.isCyclic_of_le hM'F
      have hM'ab : IsMulCommutative ↥(⁅M, M⁆ : Subgroup G) := IsCyclic.isMulCommutative
      have hM''bot : ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.2
          (Subgroup.le_centralizer_iff_isMulCommutative.2 hM'ab)
      exact hAne (le_bot_iff.1 (hM''bot ▸ (hAle.trans inf_le_right)))
    ·
      obtain ⟨-, hstruct, -⟩ := h₂ G hG M hM hnil
      obtain ⟨hsd, -, hAprime⟩ := hstruct K hKM hKhall
      obtain ⟨-, U₀, E₁, -, -, -, -, -, -, -, -, hXcent, -, -⟩ := h₅ G hamb M K hM hκ hHall
      have hcentS : ∀ k ∈ K, k ≠ 1 → sigmaCore M ⊓ centralizer ({k} : Set G) = A := by
        intro k hk hk1
        have hz := hXcent (zpowers k) (Subgroup.zpowers_le_of_mem hk)
          (fun h => hk1 (Subgroup.zpowers_eq_bot.1 h))
        rw [show Prep03.cent (sigmaCore M) ((zpowers k : Subgroup G) : Set G)
            = sigmaCore M ⊓ centralizer ((zpowers k : Subgroup G) : Set G) from rfl,
          centralizer_coe_zpowers] at hz
        exact hz
      obtain ⟨⟨-, hHallS⟩, -, hSle⟩ := h₃ G hGmin M hM
      have hcpfs := isCommonPrimeFixedSetup_subgroupOf hG.odd_natCard hMsolv hKbot hsd hnil
        hAprime (Z := A) rfl rfl hcentS hHallS hSle
      obtain ⟨hqβ, Q, hQn⟩ := mem_betaPrimes_of_isCommonPrimeFixedSetup hcpfs
      have := Fact.mk hAprime
      have := hQn
      have hmapcyc : IsCyclic ↥((hallCore ↥M).map M.subtype) := by
        rw [← hallCoreIn_eq]; exact hcyc
      have : IsCyclic ↥(hallCore ↥M) :=
        isCyclic_of_mulEquiv
          (Subgroup.equivMapOfInjective (hallCore ↥M) M.subtype M.subtype_injective).symm
      exact not_isPNarrow_of_mem_betaPrimes hqβ Q
        (isPNarrow_of_isCyclic hAprime (Subgroup.isCyclic_of_le (sylow_le_hallCore Q)))
  exact ⟨hAne, hAcyc, hAle, hnotcyc, hM'set, hcentM'⟩

end CFSG.FeitThompson.Proofs

end
