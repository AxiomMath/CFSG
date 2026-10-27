module

public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.SigmaCoreNontrivial
import CFSG.FeitThompson.Local.SigmaComplementExistsNontrivial
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.KappaPrimeLineFixedEquivalence
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup
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

open CFSG.FeitThompson Subgroup

universe u

variable {G : Type u} [Group G]

theorem exists_natCard_eq_prime_le_zpowers [Finite G] {e : G} {p : ℕ}
    (hdvd : p ∣ orderOf e) :
    ∃ P : Subgroup G, P ≤ zpowers e ∧ Nat.card ↥P = p ∧
      centralizer ({e} : Set G) ≤ centralizer (P : Set G) := by
  refine ⟨zpowers (e ^ (orderOf e / p)), ?_, ?_, ?_⟩
  · exact zpowers_le.2 (pow_mem (mem_zpowers e) _)
  · exact (Nat.card_zpowers _).trans (orderOf_pow_orderOf_div (orderOf_pos e).ne' hdvd)
  · exact centralizer_singleton_le_centralizer_zpowers_pow e _

theorem inf_centralizer_eq_bot_of_kappa_tauTwo_empty [Finite G] (hodd : Odd (Nat.card G))
    {M E : Subgroup G} (hκ : kappaPrimes M = ∅) (hτ : tauTwoPrimes M = ∅)
    (hEM : E ≤ M)
    (hdata : ∀ q ∈ _root_.CFSG.FeitThompson.primeDivisorsOf ↥E,
      elementaryAbelianPRank q ↥E = elementaryAbelianPRank q ↥M ∧
        elementaryAbelianPRank q ↥M ≤ 2)
    (hπ : _root_.CFSG.FeitThompson.primeDivisorsOf ↥E
      = _root_.CFSG.FeitThompson.primeDivisorsOf ↥M \ sigmaPrimes M)
    {e : G} (heE : e ∈ E) (he1 : e ≠ 1) :
    sigmaCore M ⊓ centralizer ({e} : Set G) = ⊥ := by
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (n := orderOf e) (by
    simpa [orderOf_eq_one_iff] using he1)
  have hordE : orderOf e ∣ Nat.card ↥E := by
    have h := orderOf_dvd_natCard (⟨e, heE⟩ : ↥E)
    rwa [← Subgroup.orderOf_coe (⟨e, heE⟩ : ↥E)] at h
  have hpE : p ∈ _root_.CFSG.FeitThompson.primeDivisorsOf ↥E := ⟨hp, hpdvd.trans hordE⟩
  have hσ : p ∉ sigmaPrimes M := (hπ ▸ hpE).2
  have hrank2 : elementaryAbelianPRank p ↥M ≤ 2 := (hdata p hpE).2
  obtain ⟨P, hPe, hPcard, hPc⟩ := exists_natCard_eq_prime_le_zpowers hpdvd
  have hPM : P ≤ M := hPe.trans (zpowers_le.2 (hEM heE))
  have hdvdM : p ∣ Nat.card ↥M := hPcard ▸ Subgroup.card_dvd_of_le hPM
  have hpodd : Odd p := (odd_natCard_subgroup hodd M).of_dvd_nat hdvdM
  have hrank1 : elementaryAbelianPRank p ↥M ≤ 1 := by
    have h1 : 1 ≤ elementaryAbelianPRank p ↥M := (one_le_elementaryAbelianPRank_iff hp).2 hdvdM
    have hne2 : elementaryAbelianPRank p ↥M ≠ 2 := fun h =>
      absurd (mem_tauTwoPrimes_iff.2 ⟨hp, hσ, h⟩) (by rw [hτ]; exact Set.notMem_empty p)
    omega
  have hcyc : ∃ S : Sylow p ↥M, IsCyclic ((S : Subgroup ↥M).map M.subtype : Subgroup G) := by
    have := Fact.mk hp
    obtain ⟨S⟩ := (Sylow.nonempty : Nonempty (Sylow p ↥M))
    exact ⟨S, (isCyclic_map_subtype_iff _).2 ((forall_isCyclic_sylow_iff hp hpodd).2 hrank1 S)⟩
  have hPbot : sigmaCore M ⊓ centralizer (P : Set G) = ⊥ := by
    by_contra hne
    exact absurd ((mem_kappaPrimes_iff_inf_centralizer_ne_bot hp hσ hcyc hPM hPcard).2 hne)
      (by rw [hκ]; exact Set.notMem_empty p)
  exact le_bot_iff.1 (hPbot ▸ inf_le_inf_left _ hPc)

theorem FTS_kappa_free_tau_two_free_frobenius
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u}) :
    Statements.FTS_kappa_free_tau_two_free_frobenius.{u} := by
  intro G _ _ hG M hM hκ hτ
  have hcoatom : IsCoatom M := hM
  have _hfin : Fintype G := Fintype.ofFinite G
  have hG2 : CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hG4 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hG8 : CFSG.FeitThompson.Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable⟩
  have hcore := (FBG_sigma_core_nontrivial h₁ G hG2 M hcoatom).2
  have huniv : ∀ E : Subgroup G, E ≤ M →
      FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E →
      ∀ e ∈ E, e ≠ 1 → sigmaCore M ⊓ centralizer ({e} : Set G) = ⊥ := by
    intro E hEM hsd e heE he1
    obtain ⟨hπ, hdata, -⟩ := FNI_sigma_complement_prime_data h₁ G hG4 M E ⟨hcoatom, hsd⟩
    exact inf_centralizer_eq_bot_of_kappa_tauTwo_empty hG.odd_natCard hκ hτ hEM hdata hπ heE he1
  obtain ⟨⟨E, hEM, hEbot, hsd⟩, -⟩ :=
    FTS_sigma_complement_exists_nontrivial h₁ G hG8 M hcoatom
  exact ⟨hcore, ⟨E, hEM, hEbot, hsd, huniv E hEM hsd⟩, huniv⟩

end

end CFSG.FeitThompson.Proofs
