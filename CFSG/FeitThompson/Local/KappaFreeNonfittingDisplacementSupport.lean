module

public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.SigmaComplementThreeHallFactors
import CFSG.FeitThompson.Local.SigmaComplementAbelianNilpotent
import CFSG.FeitThompson.Local.OutsideSigmaFixedFreeLineCommutator
import CFSG.FeitThompson.Local.SigmaHallCentralizerExcludesKappa
public import CFSG.FeitThompson.Local.PrimeActionChiefFactorsBelowFitting
import CFSG.FeitThompson.Local.ChiefFactorCentralizationFittingBound
import CFSG.FeitThompson.Local.OutsideSigmaNormalizerRankTwoPlane
import CFSG.FeitThompson.Local.KappaPrimeLineFixedEquivalence
import CFSG.FeitThompson.Local.MetabelianNonFittingPrimeDisplacement
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.Local.InvariantRankTwoFactorsFixedFreeCycle
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.CriticalSubgroupFixedLine
import CFSG.FeitThompson.Local.PComplementControlSylowNormalizer
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
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

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

universe u

theorem odd_of_prime_dvd_of_odd {n q : ℕ} (hodd : Odd n) (hq : q.Prime) (hdvd : q ∣ n) : Odd q := by
  refine hq.odd_of_ne_two ?_
  rintro rfl
  obtain ⟨k, hk⟩ := hdvd
  obtain ⟨m, hm⟩ := hodd
  omega

theorem isCyclic_sylow_of_elementaryAbelianPRank_le_one {X : Type*} [Group X] [Finite X] {q : ℕ}
    (hq : q.Prime) (hqodd : Odd q) (hrank : elementaryAbelianPRank q X ≤ 1) (S : Sylow q X) :
    IsCyclic ↥(S : Subgroup X) :=
  isCyclic_of_elementaryAbelianPRank_le_one hq hqodd S.isPGroup'
    ((elementaryAbelianPRank_subgroup_le hq.one_lt _).trans hrank)

theorem FTS_kappa_free_nonfitting_displacement_support
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₄ : Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₅ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FTS_kappa_free_nonfitting_displacement_support.{u} := by
  intro G _ _ hG q M E Q hc
  have := hG.isSimpleGroup
  have hM : IsCoatom M := hc.isCoatom
  have hEM : E ≤ M := hc.le_of_E
  have hsd := hc.isInternalSemidirectProduct
  have hqp : q.Prime := hc.prime
  have hQE : Q ≤ E := hc.le_of_Q
  have hQcard : Nat.card ↥Q = q := hc.natCard_Q
  have hQF : ¬ Q ≤ fittingOfNormal E := hc.not_le_fitting
  have hQM : Q ≤ M := hQE.trans hEM
  have : Fact q.Prime := ⟨hqp⟩
  have hFeq : (fittingRaw ↥E).map E.subtype = fittingOfNormal E := by
    rw [← subgroupOf_fittingOfNormal E, Subgroup.map_subgroupOf_eq_of_le (fittingOfNormal_le E)]
  obtain ⟨hπE, hrank, -, -, -, hπ₁, hπ₂, hπ₃⟩ :=
    FNI_sigma_complement_prime_data h₁ G
      ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩ M E ⟨hM, hsd⟩
  have hqE : q ∣ Nat.card ↥E := hQcard ▸ Subgroup.card_dvd_of_le hQE
  have hqπE : q ∈ primeDivisorsOf ↥E := ⟨hqp, hqE⟩
  have hqM : q ∣ Nat.card ↥M := hqE.trans (Subgroup.card_dvd_of_le hEM)
  have hqdiff : q ∈ primeDivisorsOf ↥M \ sigmaPrimes M := hπE ▸ hqπE
  have hqσ : q ∉ sigmaPrimes M := hqdiff.2
  have hqodd : Odd q :=
    odd_of_prime_dvd_of_odd hG.odd_natCard hqp (hqM.trans (Subgroup.card_subgroup_dvd_card M))
  obtain ⟨hrEM, -⟩ := hrank q hqπE
  have hqfac : q ∈ (Nat.card ↥E).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hqp, hqE, Nat.card_pos.ne'⟩
  have htri := mem_piOnePrimes_or_piTwoPrimes_or_piThreePrimes (X := ↥E) hqfac
  rw [piOnePrimes_eq, piTwoPrimes_eq, piThreePrimes_eq, hπ₁, hπ₂, hπ₃] at htri
  have hqτ₁ : q ∈ tau1Primes M := by
    rcases htri with h | h | h
    · exact h
    · exfalso
      have hrM2 : elementaryAbelianPRank q ↥M = 2 :=
        elementaryAbelianPRank_eq_two_of_mem_tauTwoPrimes h
      have hrE2 : elementaryAbelianPRank q ↥E = 2 := by rw [hrEM, hrM2]
      obtain ⟨A₀, he⟩ := mem_elementaryAbelianRanks.1
        (hrE2 ▸ elementaryAbelianPRank_mem_elementaryAbelianRanks (X := ↥E) (p := q) hqp.one_lt)
      have hAE : A₀.map E.subtype ≤ E := Subgroup.map_subtype_le _
      have hplane : IsElementaryAbelianPlane q (A₀.map E.subtype) := by
        obtain ⟨e⟩ := he
        exact ⟨(A₀.equivMapOfInjective E.subtype E.subtype_injective).symm.trans e⟩
      obtain ⟨hAnorm, hXA, -, -, -⟩ :=
        h₂ G ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
          q M (A₀.map E.subtype) E ⟨hM, hqp, hqσ, hAE.trans hEM, hplane⟩ ⟨hM, hsd⟩ hAE
      have hQA : Q ≤ A₀.map E.subtype := hXA Q hQE hQcard
      have hAnil : Group.IsNilpotent ↥(A₀.map E.subtype) := by
        have := hplane.isMulCommutative
        let _ : CommGroup ↥(A₀.map E.subtype) := IsMulCommutative.instCommGroup
        exact CommGroup.isNilpotent
      have hAF : A₀.map E.subtype ≤ (fittingRaw ↥E).map E.subtype :=
        le_map_fittingRaw_subtype hAE (normal_subgroupOf_of_le_normalizer hAE hAnorm) hAnil
      exact hQF (hQA.trans (hFeq ▸ hAF))
    · exfalso
      obtain ⟨E₁, E₂, E₃, hsplit, -⟩ :=
        FNI_sigma_complement_three_factors h₁ G
          ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩ M E ⟨hM, hsd⟩
      have hQpi : IsPiSubgroup (tau3Primes M) Q := by
        refine isPiSubgroup_iff.2 fun s hs => ?_
        obtain ⟨hsp, hsdvd, -⟩ := Nat.mem_primeFactors.1 hs
        rw [hQcard] at hsdvd
        rwa [(Nat.prime_dvd_prime_iff_eq hsp hqp).1 hsdvd]
      have hQE₃ : Q ≤ E₃ :=
        le_of_isHallPiSubgroup_subgroupOf hsplit.le_E₃ hsplit.outer.le_normalizer
          hsplit.isHall_E₃ hQE hQpi
      have hE₃nil : Group.IsNilpotent ↥E₃ := by
        have : IsMulCommutative ↥E₃ := @IsCyclic.isMulCommutative _ _ hsplit.isCyclic_E₃
        let _ : CommGroup ↥E₃ := IsMulCommutative.instCommGroup
        exact CommGroup.isNilpotent
      have hE₃F : E₃ ≤ (fittingRaw ↥E).map E.subtype :=
        le_map_fittingRaw_subtype hsplit.le_E₃
          (normal_subgroupOf_of_le_normalizer hsplit.le_E₃ hsplit.outer.le_normalizer) hE₃nil
      exact hQF (hQE₃.trans (hFeq ▸ hE₃F))
  have hrM1 : elementaryAbelianPRank q ↥M = 1 :=
    elementaryAbelianPRank_eq_one_of_mem_tau1Primes hqτ₁
  have hcycM : ∃ S : Sylow q ↥M, IsCyclic ((S : Subgroup ↥M).map M.subtype : Subgroup G) := by
    refine ⟨default, ?_⟩
    rw [isCyclic_map_subtype_iff]
    exact isCyclic_sylow_of_elementaryAbelianPRank_le_one hqp hqodd (le_of_eq hrM1) default
  have hSQ : sigmaCore M ⊓ centralizer (Q : Set G) = ⊥ := by
    by_contra hne
    have hmem := (mem_kappaPrimes_iff_inf_centralizer_ne_bot hqp hqσ hcycM hQM hQcard).2 hne
    rw [hc.kappaPrimes_eq_empty] at hmem
    simp at hmem
  have hE'ab : IsMulCommutative ↥(⁅E, E⁆ : Subgroup G) :=
    have : Fintype G := Fintype.ofFinite G
    (FBG_sigma_complement_abelian_nilpotent h₁ h₃ G
      ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩ M hM).2 E hsd
  have hcommE : IsMulCommutative ↥(_root_.commutator ↥E) := by
    have e := (_root_.commutator ↥E).equivMapOfInjective E.subtype E.subtype_injective
    rw [Subgroup.map_subtype_commutator] at e
    exact ⟨⟨fun a b => e.injective (by rw [map_mul, map_mul]; exact hE'ab.is_comm.comm _ _)⟩⟩
  have hrE1 : elementaryAbelianPRank q ↥E = 1 := by rw [hrEM, hrM1]
  have hcycE : ∀ S : Sylow q ↥E, IsCyclic ((S : Subgroup ↥E)) := fun S =>
    isCyclic_sylow_of_elementaryAbelianPRank_le_one hqp hqodd (le_of_eq hrE1) S
  have hQ'card : Nat.card ↥(Q.subgroupOf E) = q := by
    rw [natCard_subgroupOf_of_le' hQE, hQcard]
  have hQ'F : ¬ Q.subgroupOf E ≤ fittingRaw ↥E := by
    intro hle
    have hmap := Subgroup.map_mono (f := E.subtype) hle
    rw [Subgroup.map_subgroupOf_eq_of_le hQE, hFeq] at hmap
    exact hQF hmap
  have hDmap : (⁅(⊤ : Subgroup ↥E), Q.subgroupOf E⁆ : Subgroup ↥E).map E.subtype = ⁅E, Q⁆ := by
    rw [Subgroup.map_commutator, map_subtype_top, Subgroup.map_subgroupOf_eq_of_le hQE]
  have hDE : (⁅E, Q⁆ : Subgroup G) ≤ E := by
    rw [← hDmap]; exact Subgroup.map_subtype_le _
  have hDM : (⁅E, Q⁆ : Subgroup G) ≤ M := hDE.trans hEM
  have hDne : (⁅E, Q⁆ : Subgroup G) ≠ ⊥ := fun hbot =>
    commutator_top_left_ne_bot hqp hQ'card hQ'F (map_subtype_eq_bot_iff.1 (hDmap.trans hbot))
  have hDab : IsMulCommutative ↥(⁅E, Q⁆ : Subgroup G) := by
    have hab := isMulCommutative_commutator_top_left hcommE (Q.subgroupOf E)
    have e := (⁅(⊤ : Subgroup ↥E), Q.subgroupOf E⁆ : Subgroup ↥E).equivMapOfInjective
      E.subtype E.subtype_injective
    rw [hDmap] at e
    exact ⟨⟨fun a b => e.symm.injective (by rw [map_mul, map_mul]; exact hab.is_comm.comm _ _)⟩⟩
  have hDcardEq : Nat.card ↥(⁅E, Q⁆ : Subgroup G)
      = Nat.card ↥(⁅(⊤ : Subgroup ↥E), Q.subgroupOf E⁆ : Subgroup ↥E) := by
    rw [← hDmap, Subgroup.card_subtype]
  have hDπ : ∀ s : ℕ, s.Prime → s ∣ Nat.card ↥(⁅E, Q⁆ : Subgroup G) → s ∉ sigmaPrimes M := by
    intro s hs hsdvd
    have hsE : s ∈ primeDivisorsOf ↥E := ⟨hs, hsdvd.trans (Subgroup.card_dvd_of_le hDE)⟩
    exact (hπE ▸ hsE : s ∈ primeDivisorsOf ↥M \ sigmaPrimes M).2
  have hqD : ¬ q ∣ Nat.card ↥(⁅E, Q⁆ : Subgroup G) := by
    rw [hDcardEq]
    exact not_dvd_natCard_commutator_top_left hqp hcommE hcycE hQ'card hQ'F
  have hEND : E ≤ normalizer ((⁅E, Q⁆ : Subgroup G) : Set G) := by
    rw [← hDmap]
    exact le_normalizer_map_subtype_of_normal (normal_commutator_top_left (Q.subgroupOf E))
  have hDQself : ⁅(⁅E, Q⁆ : Subgroup G), Q⁆ = ⁅E, Q⁆ := by
    have h := commutator_commutator_top_left_eq_self (E := ↥E) (Q := Q.subgroupOf E) hqp hcommE
      hcycE hQ'card hQ'F
    have h2 := congrArg (Subgroup.map E.subtype) h
    rwa [Subgroup.map_commutator, hDmap, Subgroup.map_subgroupOf_eq_of_le hQE] at h2
  have hDQbot : (⁅E, Q⁆ : Subgroup G) ⊓ centralizer (Q : Set G) = ⊥ := by
    have h := inf_centralizer_eq_bot (E := ↥E) (Q := Q.subgroupOf E) hqp hcommE hcycE hQ'card hQ'F
    refine le_bot_iff.1 fun x hx => ?_
    obtain ⟨hxD, hxC⟩ := hx
    have hxE : x ∈ E := hDE hxD
    have hmem : (⟨x, hxE⟩ : ↥E) ∈
        (⁅(⊤ : Subgroup ↥E), Q.subgroupOf E⁆ : Subgroup ↥E) ⊓
          centralizer ((Q.subgroupOf E : Subgroup ↥E) : Set ↥E) := by
      refine ⟨?_, ?_⟩
      · rw [← hDmap] at hxD
        obtain ⟨y, hy, hyx⟩ := hxD
        exact (Subtype.ext hyx : y = (⟨x, hxE⟩ : ↥E)) ▸ hy
      · exact mem_centralizer_iff.2 fun y hy =>
          Subtype.ext ((mem_centralizer_iff.1 hxC) (y : G) (Subgroup.mem_subgroupOf.1 hy))
    rw [h, Subgroup.mem_bot] at hmem
    have hx1 : x = 1 := by simpa using congrArg Subtype.val hmem
    simp [hx1]
  obtain ⟨hDcentS, hDcyc, hMND⟩ :=
    FTS_outside_sigma_fixed_free_line_commutator h₁ h₄ h₅ G
      ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable⟩
      M (⁅E, Q⁆ : Subgroup G) Q q hM hqp hqσ hDM hDab hDπ hqD
      (le_inf (hQE.trans hEND) hQM) hQcard hSQ
  rw [hDQself] at hDcentS hDcyc hMND
  have hDnormM : ((⁅E, Q⁆ : Subgroup G).subgroupOf M).Normal :=
    normal_subgroupOf_of_le_normalizer hDM hMND
  have hDS : ⁅(⁅E, Q⁆ : Subgroup G), sigmaCore M⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.2 hDcentS
  have hτ₂ : ∀ r ∈ (Nat.card ↥(⁅E, Q⁆ : Subgroup G)).primeFactors, r ∈ tauTwoPrimes M := by
    intro r hr
    obtain ⟨hrp, hrd, -⟩ := Nat.mem_primeFactors.1 hr
    have hrσ : r ∉ sigmaPrimes M := hDπ r hrp hrd
    obtain ⟨y, hyD, hy⟩ := exists_mem_orderOf_eq_of_dvd hrp hrd
    have hXcard : Nat.card ↥(zpowers y) = r := by rw [Nat.card_zpowers, hy]
    have hXD : (zpowers y : Subgroup G) ≤ ⁅E, Q⁆ := zpowers_le.2 hyD
    have hXne : (zpowers y : Subgroup G) ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at hXcard
      exact hrp.one_lt.ne hXcard
    have hXp : IsPGroup r (zpowers y) := IsPGroup.of_card (by rw [pow_one, hXcard])
    have := hDcyc
    have hMNX : M ≤ normalizer ((zpowers y : Subgroup G) : Set G) :=
      le_normalizer_of_le_of_isCyclic hXD hMND
    have hNtop : normalizer ((zpowers y : Subgroup G) : Set G) ≠ ⊤ :=
      (normalizer_lt_top_of_isPGroup hG.not_isMulCommutative hrp hXne hXp).ne
    have hNM : normalizer ((zpowers y : Subgroup G) : Set G) ≤ M := by
      rcases eq_or_lt_of_le hMNX with h | h
      · exact h.ge
      · exact absurd (hM.2 _ h) hNtop
    have hrank2 : elementaryAbelianPRank r ↥M = 2 :=
      elementaryAbelianPRank_eq_two_of_notMem_sigmaPrimes hG.not_isMulCommutative hG.odd_natCard
        hG.isSolvable hM hrp hrσ hXcard hNM
    exact mem_tauTwoPrimes_iff.2 ⟨hrp, hrσ, hrank2⟩
  exact ⟨hqτ₁, hSQ, hDne, hDcyc, hDnormM, hDQself, hDQbot, hDS, hτ₂⟩

end

end CFSG.FeitThompson.Proofs
