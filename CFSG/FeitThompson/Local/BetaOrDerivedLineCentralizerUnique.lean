module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.BetaPrimesSigmaCompatibility
import CFSG.FeitThompson.Local.NormalComplementSylowDerivedIntersection
import CFSG.FeitThompson.Local.RegularTauAlphaFixedPoints
import CFSG.FeitThompson.Local.NormalPlaneElementCentralizerIndex
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.SmallCentralizerLineMissesDerived
import CFSG.FeitThompson.Local.ConjugationUniqueMaximalOvergroup
import CFSG.FeitThompson.Local.PrimeExtensionMaximalInvariantSubgroup
import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.OddOrder.RankThreeUniquenessMaximalOvergroup
import CFSG.FeitThompson.OddOrder.SigmaHallSubgroupNormalizer
import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction
import CFSG.FeitThompson.Local.BetaPrimeDerivedComplement
import CFSG.FeitThompson.Local.LowRankAmbientSylowDerivedCentral
import CFSG.FeitThompson.Local.NonabelianPrimeSubgroupUniqueMaximum
import CFSG.FeitThompson.Local.SigmaConjugateIntersectionCyclic
import CFSG.FeitThompson.Local.AbelianAmbientNormalHallInertiaExponent
import CFSG.FeitThompson.Local.CommonSylowNormalizerBetaFactor
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

variable {G : Type*} [Group G]

theorem map_subtype_commutator_eq_commutator (S : Subgroup G) :
    Subgroup.map S.subtype (_root_.commutator ↥S) = ⁅S, S⁆ := by
  have hmapS : Subgroup.map S.subtype (⊤ : Subgroup ↥S) = S :=
    le_antisymm (Subgroup.map_subtype_le _) fun x hx => ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  rw [_root_.commutator_def, Subgroup.map_commutator, hmapS]

theorem subgroupOf_le_of_le_map_subtype {S : Subgroup G} {C : Subgroup ↥S} {X : Subgroup G}
    (h : X ≤ Subgroup.map S.subtype C) : X.subgroupOf S ≤ C := by
  intro x hx
  obtain ⟨y, hyC, hy⟩ := h (mem_subgroupOf.1 hx)
  have hyx : y = x := Subtype.ext hy
  exact hyx ▸ hyC

theorem FTS_beta_or_derived_line_centralizer_unique
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₃ : Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₄ : Statements.FTS_nonunique_line_centralizer_bounds.{u})
    (h₅ : Statements.FTS_plane_maximal_overgroups.{u})
    (h₆ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FTS_beta_or_derived_line_centralizer_unique.{u} := by
  intro G _ _ hG M X hM p hp hXM hXcard hor
  have hMc : IsCoatom M := hM
  have hsimple : IsSimpleGroup G := hG.simple
  have := Fact.mk hp
  obtain ⟨hHallOf, hHallG, -⟩ :=
    h₁ G (by
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        first
          | exact hG.odd
          | exact hG.simple
          | exact hG.nonabelian
          | exact hG.solvable) M hMc
  have hXne : X ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hXcard
    exact hp.one_lt.ne hXcard
  have hXp : IsPGroup p ↥X := IsPGroup.of_card (n := 1) (by rw [hXcard, pow_one])
  have hpσ : p ∈ sigmaPrimes M := by
    rcases hor with hβ | hder
    · exact betaPrimes_subset_sigmaPrimes hG.nonabelian hG.odd hG.solvable hMc hβ
    · exact mem_sigmaPrimes_of_isPGroup_le_sigmaCore hp hXne hXp
        (hder.trans (Subgroup.commutator_le_self _))
  have hXS : X ≤ sigmaCore M := by
    have hXpi : IsPiSubgroup (sigmaPrimes M) (X.subgroupOf M) := by
      refine isPiSubgroup_iff.2 fun r hr => ?_
      rw [natCard_subgroupOf hXM, hXcard, hp.primeFactors, Finset.mem_singleton] at hr
      exact hr ▸ hpσ
    have h := Subgroup.map_mono (f := M.subtype) (hHallOf.2.le_of_isPiSubgroup hXpi)
    rwa [Subgroup.map_subgroupOf_eq_of_le hXM,
      Subgroup.map_subgroupOf_eq_of_le hHallOf.1] at h
  obtain ⟨P, hPS, hXP, hPcardS⟩ :
      ∃ P : Subgroup G, P ≤ sigmaCore M ∧ X ≤ P ∧
        Nat.card ↥P = p ^ (Nat.card ↥(sigmaCore M)).factorization p := by
    obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow (p := p)
      (P := X.subgroupOf (sigmaCore M))
      (IsPGroup.of_card (n := 1) (by rw [natCard_subgroupOf hXS, hXcard, pow_one]))
    refine ⟨Subgroup.map (sigmaCore M).subtype (Q : Subgroup ↥(sigmaCore M)),
      Subgroup.map_subtype_le _, ?_, ?_⟩
    · have h := Subgroup.map_mono (f := (sigmaCore M).subtype) hQ
      rwa [Subgroup.map_subgroupOf_eq_of_le hXS] at h
    · rw [Subgroup.card_map_of_injective (sigmaCore M).subtype_injective]
      exact Q.card_eq_multiplicity
  have hPM : P ≤ M := hPS.trans (sigmaCore_le M)
  have hfactG : (Nat.card ↥(sigmaCore M)).factorization p = (Nat.card G).factorization p :=
    factorization_natCard_eq_of_isHallPiSubgroup_mem hHallG hp hpσ
  have hfactM : (Nat.card ↥M).factorization p = (Nat.card ↥(sigmaCore M)).factorization p :=
    factorization_natCard_eq_of_isHallPiSubgroup_subgroupOf hp hHallOf.1 hHallOf.2 hpσ
  have hPcardG : Nat.card ↥P = p ^ (Nat.card G).factorization p := by
    rw [hPcardS, hfactG]
  have hPcardM : Nat.card ↥(P.subgroupOf M) = p ^ (Nat.card ↥M).factorization p := by
    rw [natCard_subgroupOf hPM, hPcardS, hfactM]
  have hPp : IsPGroup p ↥P := IsPGroup.of_card hPcardG
  have hPne : P ≠ ⊥ := fun h => hXne (le_bot_iff.1 (h ▸ hXP))
  have hPlt : P < ⊤ := lt_top_of_isPGroup hG.nonabelian hp hPne hPp
  have hpodd : Odd p := by
    refine hG.odd.of_dvd_nat ?_
    rw [← hXcard]
    exact (Subgroup.card_dvd_of_le le_top).trans (by simp)
  have hCne : centralizer (X : Set G) ≠ ⊤ := by
    intro hC
    have hcen : Subgroup.center G = ⊥ := by
      rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h1 | h1
      · exact h1
      · refine absurd (IsMulCommutative.of_comm fun a b => ?_) hG.nonabelian
        have ha : a ∈ Subgroup.center G := by rw [h1]; exact Subgroup.mem_top a
        exact ((Subgroup.mem_center_iff.1 ha) b).symm
    have hXcen : X ≤ Subgroup.center G := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ centralizer (X : Set G) := by rw [hC]; exact Subgroup.mem_top g
      exact ((Subgroup.mem_centralizer_iff.1 hg) x hx).symm
    exact hXne (le_bot_iff.1 (hcen ▸ hXcen))
  have hboth : IsUniqueMaximalOvergroup P M ∧
      IsUniqueMaximalOvergroup (centralizer (X : Set G)) M := by
    by_cases hrank : 3 ≤ elementaryAbelianPRank p ↥(P ⊓ centralizer (X : Set G))
    ·
      have hne : (P ⊓ centralizer (X : Set G)) ≠ ⊤ := by
        intro h
        have hle : (⊤ : Subgroup G) ≤ P :=
          h ▸ (inf_le_left : P ⊓ centralizer (X : Set G) ≤ P)
        exact hPlt.ne (top_le_iff.1 hle)
      obtain ⟨N, hN⟩ := exists_isUniqueMaximalOvergroup_of_three_le_maxElementaryAbelianPRank
        hG.nonabelian hG.odd hG.solvable hne
        (le_trans hrank (elementaryAbelianPRank_le_maxElementaryAbelianPRank hp))
      have hNM : M = N := hN.eq_of_isCoatom hMc (inf_le_left.trans hPM)
      have hN' : IsUniqueMaximalOvergroup (P ⊓ centralizer (X : Set G)) M := by
        rw [hNM]; exact hN
      exact ⟨hN'.mono inf_le_left hPlt.ne, hN'.mono inf_le_right hCne⟩
    ·
      have hle2 : elementaryAbelianPRank p ↥(P ⊓ centralizer (X : Set G)) ≤ 2 := by omega
      have hXPcard : Nat.card ↥(X.subgroupOf P) = p := by
        rw [natCard_subgroupOf hXP, hXcard]
      have hCrank :
          elementaryAbelianPRank p
            ↥(centralizer ((X.subgroupOf P : Subgroup ↥P) : Set ↥P)) ≤ 2 := by
        rw [centralizer_subgroupOf hXP,
          elementaryAbelianPRank_subgroupOf hp.one_lt (inf_le_left : _ ≤ P)]
        exact hle2
      have hnarrow : IsPNarrow p ↥P := by
        by_cases hr : elementaryAbelianPRank p ↥P ≤ 2
        · exact isPNarrow_of_elementaryAbelianPRank_le_two hr
        · have hr3 : 3 ≤ elementaryAbelianPRank p ↥P := by omega
          obtain ⟨a, hPa⟩ := hPp.exists_card_eq
          have ha : 1 ≤ a := by
            rcases Nat.eq_zero_or_pos a with rfl | hpos
            · exfalso
              have : Subsingleton ↥P := (Nat.card_eq_one_iff_unique.1 (by simpa using hPa)).1
              rw [elementaryAbelianPRank_eq_zero_of_subsingleton hp.one_lt] at hr3
              omega
            · exact hpos
          obtain ⟨Z, hZ, hZc⟩ := exists_le_center_natCard_eq hp hPa ha
          have hmax := maximal_isElementaryAbelian_sup hp hr3 hCrank hXPcard hZ hZc
          have hcard :=
            natCard_sup_eq_sq_of_elementaryAbelianPRank_centralizer_le hp hr3 hCrank hXPcard hZ hZc
          have hEA : ∀ {A : Subgroup ↥P},
              IsElementaryAbelian p A ↔ IsElementaryAbelianSubgroup p A :=
            isElementaryAbelian_iff.trans isElementaryAbelianSubgroup_iff.symm
          refine isPNarrow_of_maximal_card_eq
            ⟨hEA.1 hmax.prop, fun B hB hle => hmax.le_of_ge (hEA.2 hB) hle⟩ hcard
      have hpβM : p ∉ betaPrimes ↥M := by
        intro hβ
        refine not_isPNarrow_of_mem_betaPrimes hβ (Sylow.ofCard (P.subgroupOf M) hPcardM) ?_
        rw [Sylow.coe_ofCard]
        exact (isPNarrow_congr hp.one_lt (Subgroup.subgroupOfEquivOfLe hPM)).2 hnarrow
      have hXder : X ≤ ⁅sigmaCore M, sigmaCore M⁆ := hor.resolve_left hpβM
      obtain ⟨-, -, -, hKnorm, hKcard, k, hKidx⟩ :=
        FTS_beta_prime_derived_complement h₁ h₆ G hG M hM p hp hpodd hpβM
      have hKle : _root_.CFSG.FeitThompson.Prep06.pComplCoreIn p (sigmaCore M) ≤ sigmaCore M :=
        Subgroup.map_subtype_le _
      letI := hKnorm
      have hKcard' :
          ¬ p ∣ Nat.card ↥((_root_.CFSG.FeitThompson.Prep06.pComplCoreIn p
            (sigmaCore M)).subgroupOf (sigmaCore M)) := by
        rw [natCard_subgroupOf hKle]; exact hKcard
      have hKidx' :
          ((_root_.CFSG.FeitThompson.Prep06.pComplCoreIn p
            (sigmaCore M)).subgroupOf (sigmaCore M)).index = p ^ k := by
        rw [index_subgroupOf]; exact hKidx
      have hXPder : X ≤ ⁅P, P⁆ := by
        have hQcard : Nat.card ↥(P.subgroupOf (sigmaCore M))
            = p ^ (Nat.card ↥(sigmaCore M)).factorization p := by
          rw [natCard_subgroupOf hPS, hPcardS]
        have hinf := sylow_inf_commutator_eq_commutator hp hKcard' hKidx'
          (Sylow.ofCard (P.subgroupOf (sigmaCore M)) hQcard)
        rw [Sylow.coe_ofCard] at hinf
        have hXcomm : X.subgroupOf (sigmaCore M) ≤ _root_.commutator ↥(sigmaCore M) :=
          subgroupOf_le_of_le_map_subtype
            (by rw [map_subtype_commutator_eq_commutator]; exact hXder)
        have h1 : X.subgroupOf (sigmaCore M) ≤
            ⁅P.subgroupOf (sigmaCore M), P.subgroupOf (sigmaCore M)⁆ := by
          rw [← hinf]
          exact le_inf (Subgroup.subgroupOf_mono (sigmaCore M) hXP) hXcomm
        have h2 := Subgroup.map_mono (f := (sigmaCore M).subtype) h1
        rwa [Subgroup.map_subgroupOf_eq_of_le hXS, Subgroup.map_commutator,
          Subgroup.map_subgroupOf_eq_of_le hPS] at h2
      have hrP2 : elementaryAbelianPRank p ↥P ≤ 2 := by
        by_contra hrP
        have hr3 : 3 ≤ elementaryAbelianPRank p ↥P := by omega
        have hbot := inf_commutator_eq_bot_of_elementaryAbelianPRank_centralizer_le
          (P := ↥P) (X := X.subgroupOf P) hp hpodd hPp hr3 hXPcard hCrank
        have h1 : X.subgroupOf P ≤ _root_.commutator ↥P :=
          subgroupOf_le_of_le_map_subtype
            (by rw [map_subtype_commutator_eq_commutator]; exact hXPder)
        have h2 : X.subgroupOf P = ⊥ := le_bot_iff.1 (hbot ▸ le_inf le_rfl h1)
        have h3 := Subgroup.map_subgroupOf_eq_of_le hXP
        rw [h2] at h3
        exact hXne (by simpa using h3.symm)
      have hcentral := FTS_low_rank_ambient_sylow_derived_central h₆ G
        (by
          refine ⟨?_, ?_, ?_, ?_⟩ <;>
            first
              | exact hG.odd
              | exact hG.simple
              | exact hG.nonabelian
              | exact hG.solvable) p hp hpodd (Sylow.ofCard P hPcardG)
        (by rw [Sylow.coe_ofCard]; exact hrP2)
      rw [Sylow.coe_ofCard] at hcentral
      have hXcP : X ≤ centralizer (P : Set G) := (hXPder.trans hcentral).trans inf_le_right
      have hPcX : P ≤ centralizer (X : Set G) := by
        intro g hg
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact ((Subgroup.mem_centralizer_iff.1 (hXcP hx)) g hg).symm
      have hPna : ¬ IsMulCommutative ↥P := by
        intro hcomm
        have hle : P ≤ centralizer (P : Set G) := by
          intro g hg
          rw [Subgroup.mem_centralizer_iff]
          intro m hm
          have h := hcomm.is_comm.comm (⟨m, hm⟩ : ↥P) (⟨g, hg⟩ : ↥P)
          simpa using congrArg Subtype.val h
        have hbot : (⁅P, P⁆ : Subgroup G) = ⊥ :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.2 hle
        exact hXne (le_bot_iff.1 (hbot ▸ hXPder))
      obtain ⟨a, hPa⟩ := hPp.exists_card_eq
      have ha : 1 ≤ a := by
        rcases Nat.eq_zero_or_pos a with rfl | hpos
        · exact absurd (Subgroup.card_eq_one.1 (by simpa using hPa)) hPne
        · exact hpos
      obtain ⟨M', -, huniq⟩ :=
        FNI_nonabelian_prime_subgroup_unique_maximum h₁ h₂ h₃ h₄ h₅ h₆ G
          (by
            refine ⟨?_, ?_, ?_, ?_⟩ <;>
              first
                | exact hG.odd
                | exact hG.simple
                | exact hG.nonabelian
                | exact hG.solvable) p a P hp ha hPa hPna
      have hPuniq : IsUniqueMaximalOvergroup P M := by
        refine ⟨hMc, hPM, fun N hN hPN => ?_⟩
        exact (huniq N ⟨hN, hPN⟩).trans (huniq M ⟨hMc, hPM⟩).symm
      exact ⟨hPuniq, hPuniq.mono hPcX hCne⟩
  obtain ⟨hPuniq, hCuniq⟩ := hboth
  refine ⟨hCuniq, fun P' hP' => ?_⟩
  obtain ⟨e, heS, hePP'⟩ :=
    exists_mem_map_conj_eq_of_le (E := sigmaCore M) hPS hP'.1 hPcardS hP'.2
  have heM : e ∈ M := sigmaCore_le M heS
  have hMfix : MulAut.conj e • M = M :=
    conj_smul_eq_self_iff_mem_normalizer.2 (Subgroup.le_normalizer heM)
  have hconj := hPuniq.smul e
  rwa [hMfix, conj_smul_eq_map_conj, hePP'] at hconj

end

end CFSG.FeitThompson.Proofs
