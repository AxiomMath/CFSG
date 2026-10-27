module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.NonregularComplementElementTauTwoPrimes
import CFSG.FeitThompson.Local.TauTwoSubgroupCentralizerUnique
import CFSG.FeitThompson.Local.UniqueMaximalOvergroupCentralizerTauOneThree
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.KappaFreeTauTwoFreeFrobenius
import CFSG.FeitThompson.Local.SigmaPrimeNormalizerOutsideComplement
import CFSG.FeitThompson.Local.KappaPrimeLineFixedEquivalence
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup
public import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup
open CFSG.FeitThompson.Prep05 (centralizerIn)
open CFSG.FeitThompson.Prep09 (centIn)

universe u

variable {G : Type u} [Group G]

theorem mem_kappaPrimes_of_dvd_orderOf [Finite G] (hodd : Odd (Nat.card G))
    {M E : Subgroup G} (hEM : E ≤ M)
    (hdata : ∀ q ∈ _root_.CFSG.FeitThompson.primeDivisorsOf ↥E,
      elementaryAbelianPRank q ↥E = elementaryAbelianPRank q ↥M ∧
        elementaryAbelianPRank q ↥M ≤ 2)
    {y : G} (hyE : y ∈ E) {p : ℕ} (hp : p.Prime) (hpy : p ∣ orderOf y)
    (hpσ : p ∉ sigmaPrimes M) (hpτ : p ∉ tauTwoPrimes M)
    (hCy : sigmaCore M ⊓ centralizer ({y} : Set G) ≠ ⊥) :
    p ∈ kappaPrimes M ∧ p ∈ tau1Primes M ∪ tau3Primes M ∧
      ∃ P : Subgroup G, P ≤ E ∧ Nat.card ↥P = p ∧
        centralizer ({y} : Set G) ≤ centralizer (P : Set G) ∧
        sigmaCore M ⊓ centralizer (P : Set G) ≠ ⊥ := by
  obtain ⟨P, hPy, hPcard, hPc⟩ := exists_natCard_eq_prime_le_zpowers hpy
  have hPE : P ≤ E := hPy.trans (zpowers_le.2 hyE)
  have hPM : P ≤ M := hPE.trans hEM
  have hCP : sigmaCore M ⊓ centralizer (P : Set G) ≠ ⊥ := fun h =>
    hCy (le_bot_iff.1 (h ▸ inf_le_inf_left (sigmaCore M) hPc))
  have hpE : p ∣ Nat.card ↥E := hpy.trans (E.orderOf_dvd_natCard hyE)
  have hpM : p ∣ Nat.card ↥M := hpE.trans (Subgroup.card_dvd_of_le hEM)
  have hrank2 : elementaryAbelianPRank p ↥M ≤ 2 := (hdata p ⟨hp, hpE⟩).2
  have hrank1 : 1 ≤ elementaryAbelianPRank p ↥M := (one_le_elementaryAbelianPRank_iff hp).2 hpM
  have hrank : elementaryAbelianPRank p ↥M = 1 := by
    rcases Nat.lt_or_ge (elementaryAbelianPRank p ↥M) 2 with h | h
    · omega
    · exact absurd (mem_tauTwoPrimes_iff.2 ⟨hp, hpσ, by omega⟩) hpτ
  have hpodd : Odd p := (odd_natCard_subgroup hodd M).of_dvd_nat hpM
  have hcyc : ∃ S : Sylow p ↥M, IsCyclic ((S : Subgroup ↥M).map M.subtype : Subgroup G) := by
    have := Fact.mk hp
    obtain ⟨S⟩ := (Sylow.nonempty : Nonempty (Sylow p ↥M))
    exact ⟨S, (isCyclic_map_subtype_iff _).2
      ((forall_isCyclic_sylow_iff hp hpodd).2 (by omega) S)⟩
  refine ⟨(mem_kappaPrimes_iff_inf_centralizer_ne_bot hp hpσ hcyc hPM hPcard).2 hCP, ?_,
    P, hPE, hPcard, hPc, hCP⟩
  rw [tau1Primes_union_tau3Primes]
  exact ⟨hp, hpM, hpσ, hrank⟩

theorem FTS_core_centralizing_external_element_dichotomy
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_hall_abelian.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_tau12_fixed_plane_line_core_free.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FNI_tau13_nonfree_third_factor_structure.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_fixed_line_centralizer_unique.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_core_centralizing_external_element_dichotomy.{u} := by
  intro G _ _ hG M hM x hx hx1 y hy hy1 hyσ
  have hcoatom : IsCoatom M := hM
  have := hG.isSimpleGroup
  have hG04 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hG05 : CFSG.FeitThompson.Prep05.IsMinimalSimpleOdd G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hG09 : CFSG.FeitThompson.Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  obtain ⟨hyM, hyC⟩ := Subgroup.mem_inf.1 hy
  have hxy : x ∈ centralizer ({y} : Set G) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 hyC).symm
  have hCy : sigmaCore M ⊓ centralizer ({y} : Set G) ≠ ⊥ := fun h =>
    hx1 (Subgroup.mem_bot.1 (h ▸ Subgroup.mem_inf.2 ⟨hx, hxy⟩))
  have hyzM : (zpowers y : Subgroup G) ≤ M := zpowers_le.2 hyM
  obtain ⟨E, hyE', hsd⟩ :=
    exists_isInternalSemidirectProduct_sigmaCore_ge hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable hcoatom hyzM (isPiSubgroup_iff.2 (by rw [Nat.card_zpowers]; exact hyσ))
  have hEM : E ≤ M := hsd.right_le
  have hyE : y ∈ E := hyE' (mem_zpowers y)
  by_cases hex : ∃ r ∈ (orderOf y).primeFactors, r ∈ tauTwoPrimes M
  ·
    have hτ : ∀ r ∈ (orderOf y).primeFactors, r ∈ tauTwoPrimes M :=
      FTS_core_nonregular_element_with_tau_two_prime h₁ h₄ h₅ h₆ h₇ h₈ G hG M hM E hEM hsd y hyE
        hy1 hCy hex
    have hyne : (zpowers y : Subgroup G) ≠ ⊥ := fun h =>
      hy1 (Subgroup.mem_bot.1 (h ▸ mem_zpowers y))
    have hcent : centIn (sigmaCore M) ((zpowers y : Subgroup G) : Set G) ≠ ⊥ := by
      rw [CFSG.FeitThompson.Prep09.centIn_def,
        centralizer_coe_zpowers]
      exact hCy
    have hres := FTS_tau_two_subgroup_centralizer_unique h₂ h₃ G hG09 M hcoatom (zpowers y) hyzM
      hyne (by rw [Nat.card_zpowers]; exact hτ) hcent
    refine Or.inr ⟨hτ, ?_⟩
    rw [← centralizer_coe_zpowers y]
    exact hres.2
  ·
    obtain ⟨-, hrank, -⟩ := FNI_sigma_complement_prime_data h₁ G hG04 M E ⟨hcoatom, hsd⟩
    have hkey : ∀ r ∈ (orderOf y).primeFactors,
        r ∈ kappaPrimes M ∧ r ∈ tau1Primes M ∪ tau3Primes M ∧
          ∃ P : Subgroup G, P ≤ E ∧ Nat.card ↥P = r ∧
            centralizer ({y} : Set G) ≤ centralizer (P : Set G) ∧
            sigmaCore M ⊓ centralizer (P : Set G) ≠ ⊥ := by
      intro r hr
      obtain ⟨hrp, hrd, -⟩ := Nat.mem_primeFactors.1 hr
      exact mem_kappaPrimes_of_dvd_orderOf hG.odd_natCard hEM hrank hyE hrp hrd (hyσ r hr)
        (fun h => hex ⟨r, hr, h⟩) hCy
    refine Or.inl ⟨fun r hr => (hkey r hr).1, ?_⟩
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (n := orderOf y)
      fun h => hy1 (orderOf_eq_one_iff.1 h)
    obtain ⟨-, hpτ13, P, hPE, hPcard, hPc, hCP⟩ :=
      hkey p (Nat.mem_primeFactors.2 ⟨hp, hpdvd, (orderOf_pos y).ne'⟩)
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd (n := orderOf x)
      fun h => hx1 (orderOf_eq_one_iff.1 h)
    obtain ⟨Q, hQx, hQcard, hQc⟩ := exists_natCard_eq_prime_le_zpowers hqdvd
    have hQcentIn : Q ≤ centralizerIn (sigmaCore M) P :=
      le_inf (hQx.trans (zpowers_le.2 hx)) (hQx.trans ((zpowers_le.2 hxy).trans hPc))
    have huniq := FNI_tau13_nonregular_core_line_unique h₁ h₆ h₉ G hG05 M E ⟨hcoatom, hsd⟩ p hpτ13
      P hPE hPcard hCP q hq Q hQcentIn hQcard
    exact (le_trans hQc huniq.le : centralizer ({x} : Set G) ≤ M)

end

end CFSG.FeitThompson.Proofs
