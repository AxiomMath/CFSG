module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.HallTauTwoSubgroupsAbelian
import CFSG.FeitThompson.Local.AbelianHallTauTwoControlsCentralizers
import CFSG.FeitThompson.Local.TwoBetaFixedCoresHallPosition
import CFSG.FeitThompson.Local.OutsideSigmaKappaSylowCoreNilpotent
import CFSG.FeitThompson.Local.NonabelianAmbientNormalHallFreeComplement
import CFSG.FeitThompson.Local.CriticalSubgroupFixedLine
import CFSG.FeitThompson.Local.NoSigmaKappaPrimesRankTwoPrimes
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson
open CFSG.FeitThompson.Prep09

universe u

variable {G : Type*} [Group G]

private theorem natCard_subgroupOf_of_le_aux {H K : Subgroup G} (h : H ≤ K) :
    Nat.card ↥(H.subgroupOf K) = Nat.card ↥H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem maxElementaryAbelianPRank_le_of_isPGroup {p n : ℕ} {Q : Type*} [Group Q] [Finite Q]
    (hp : p.Prime) (hQ : IsPGroup p Q) (h : elementaryAbelianPRank p Q ≤ n) :
    maxElementaryAbelianPRank Q ≤ n := by
  have hfp : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  refine maxElementaryAbelianPRank_le fun d hd => ?_
  obtain ⟨q, hq, hd⟩ := mem_elementaryAbelianPrimeRanks.1 hd
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · exact Nat.zero_le _
  · obtain ⟨A, hA⟩ := exists_subgroup_card_eq_of_mem_elementaryAbelianRanks hd
    have hdvd : q ∣ Nat.card Q :=
      (dvd_pow_self q (by omega)).trans (hA ▸ A.card_subgroup_dvd_card)
    have hqp : q = p := by
      rw [hk] at hdvd
      exact (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hdvd)
    subst hqp
    exact (le_elementaryAbelianPRank hq.one_lt hd).trans h

theorem FTS_type_I_complement_structure
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FPL_low_rank_sylow_central_product.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_nonunique_line_centralizer_bounds.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_core_kappa_identity.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_type_I_complement_structure.{u} := by
  intro G _ _ hG M hM hMI U hUcompl
  have hsimple : IsSimpleGroup G := hG.isSimpleGroup
  have _inst : Fintype G := Fintype.ofFinite G
  have hG4 : CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG2 : CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG6 : _root_.CFSG.FeitThompson.Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨hκ, hHS, hUσ⟩ := h₉ G hG M hM hMI
  obtain ⟨hUM, hprod0, hinf0⟩ := hUcompl
  have hprod : (sigmaCore M : Set G) * (U : Set G) = (M : Set G) := by rw [← hHS]; exact hprod0
  have hinf : sigmaCore M ⊓ U = ⊥ := by rw [← hHS]; exact hinf0
  have hSM : sigmaCore M ≤ M := (isGreatest_sigmaCore M).1.1
  have hSpi : ∀ s ∈ (Nat.card ↥(sigmaCore M)).primeFactors, s ∈ sigmaPrimes M :=
    isPiSubgroup_iff.1 (isGreatest_sigmaCore M).1.2.2
  have hsup : sigmaCore M ⊔ U = M := by
    refine le_antisymm (sup_le hSM hUM) fun x hx => ?_
    have hx' : x ∈ (sigmaCore M : Set G) * (U : Set G) := by rw [hprod]; exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    exact mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
  have hsemi : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) U :=
    ⟨hsup, le_normalizer_sigmaCore M, disjoint_iff.2 hinf⟩
  have hUne : U ≠ ⊤ := fun h => hM.1 (top_le_iff.1 (h ▸ hUM))
  have hUsolv : Group.IsSolvable ↥U := hG.isSolvable_of_ne_top U hUne
  have hUσ' : ∀ s : ℕ, s.Prime → s ∣ Nat.card ↥U → s ∉ sigmaPrimes M := fun s hs hsU =>
    hUσ U ⟨hUM, hprod0, hinf0⟩ s (Nat.mem_primeFactors.2 ⟨hs, hsU, Nat.card_pos.ne'⟩)
  refine ⟨?_, ?_⟩
  ·
    intro p hp P
    have hfp : Fact p.Prime := ⟨hp⟩
    have hequiv : ↥(P : Subgroup ↥U) ≃* ↥((P : Subgroup ↥U).map U.subtype) :=
      Subgroup.equivMapOfInjective _ _ U.subtype_injective
    have hQU : (P : Subgroup ↥U).map U.subtype ≤ U := Subgroup.map_subtype_le _
    have hQM : (P : Subgroup ↥U).map U.subtype ≤ M := hQU.trans hUM
    have hQpg : IsPGroup p ↥((P : Subgroup ↥U).map U.subtype) := P.isPGroup'.of_equiv hequiv
    have hQcard : Nat.card ↥((P : Subgroup ↥U).map U.subtype)
        = p ^ (Nat.card ↥U).factorization p := by
      rw [Subgroup.card_subtype, P.card_eq_multiplicity]
    by_cases hpU : p ∣ Nat.card ↥U
    · have hpσ : p ∉ sigmaPrimes M := hUσ' p hp hpU
      have hpodd : Odd p := by
        rcases hp.eq_two_or_odd with h | h
        · exfalso
          have h1 : Nat.card G % 2 = 1 := Nat.odd_iff.1 hG.odd_natCard
          obtain ⟨c, hc⟩ := (h ▸ hpU : (2 : ℕ) ∣ Nat.card ↥U).trans
            (Subgroup.card_subgroup_dvd_card U)
          omega
        · exact Nat.odd_iff.2 h
      have hpS : ¬ p ∣ Nat.card ↥(sigmaCore M) := fun hdvd =>
        hpσ (hSpi p (Nat.mem_primeFactors.2 ⟨hp, hdvd, Nat.card_pos.ne'⟩))
      have hfact : (Nat.card ↥M).factorization p = (Nat.card ↥U).factorization p := by
        rw [hsemi.natCard_eq_mul, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
        simp [Nat.factorization_eq_zero_of_not_dvd hpS]
      have hQsyl : _root_.CFSG.FeitThompson.IsSylowIn p M
          ((P : Subgroup ↥U).map U.subtype) :=
        (_root_.CFSG.FeitThompson.isSylowIn_iff_natCard hp hQM).2 (by rw [hQcard, hfact])
      have key : IsMulCommutative ↥((P : Subgroup ↥U).map U.subtype) ∧
          elementaryAbelianPRank p ↥((P : Subgroup ↥U).map U.subtype) ≤ 2 := by
        by_cases hr2 : 2 ≤ elementaryAbelianPRank p ↥((P : Subgroup ↥U).map U.subtype)
        ·
          obtain ⟨A, hAQ, hAplane⟩ := exists_isElementaryAbelianPlane_le hp hr2
          obtain ⟨e⟩ := hAplane
          have hos : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane p M A :=
            ⟨hM, hp, hpσ, hAQ.trans hQM, ⟨e⟩⟩
          have hsyl := h₄ G hG4 p M A hos
          refine ⟨(hsyl.2.2.1 _ hQsyl).1, ?_⟩
          have hle := elementaryAbelianPRank_le_of_le (p := p) hp.one_lt hQM
          rw [hsyl.1] at hle
          exact hle
        ·
          have hr1 : elementaryAbelianPRank p ↥((P : Subgroup ↥U).map U.subtype) ≤ 1 := by
            omega
          have hcyc : IsCyclic ↥((P : Subgroup ↥U).map U.subtype) :=
            isCyclic_of_elementaryAbelianPRank_le_one hp hpodd hQpg hr1
          exact ⟨IsCyclic.isMulCommutative, by omega⟩
      refine ⟨isMulCommutative_of_map_subtype key.1, ?_⟩
      rw [maxElementaryAbelianPRank_eq_of_mulEquiv hequiv]
      exact maxElementaryAbelianPRank_le_of_isPGroup hp hQpg key.2
    ·
      have hcard1 : Nat.card ↥(P : Subgroup ↥U) = 1 := by
        rw [P.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hpU, pow_zero]
      have hss : Subsingleton ↥(P : Subgroup ↥U) := (Nat.card_eq_one_iff_unique.1 hcard1).1
      refine ⟨IsMulCommutative.of_comm fun a b => Subsingleton.elim _ _, ?_⟩
      rw [(maxElementaryAbelianPRank_eq_zero_iff _).2 hss]
      omega
  ·
    intro X hXU hXbot hXc
    rw [centIn_def, hHS] at hXc
    have hXM : X ≤ M := hXU.trans hUM
    have hXdvd : Nat.card ↥X ∣ Nat.card ↥U := Subgroup.card_dvd_of_le hXU
    have hXsk : ∀ r ∈ (Nat.card ↥X).primeFactors, r ∉ sigmaPrimes M ∪ kappaPrimes M := by
      intro r hr
      have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
      have hrU : r ∣ Nat.card ↥U := (Nat.dvd_of_mem_primeFactors hr).trans hXdvd
      simp only [Set.mem_union, not_or]
      exact ⟨hUσ' r hrp hrU, by rw [hκ]; exact Set.notMem_empty r⟩
    have hXpi : IsPiSubgroup (tauTwoPrimes M) X :=
      isPiSubgroup_iff.2 fun s hs => primeFactors_subset_tauTwoPrimes hG.not_isMulCommutative
        hG.odd_natCard hG.isSolvable_of_ne_top hM hXM hXsk hXc (Finset.mem_coe.2 hs)
    obtain ⟨E₂, hE₂hall, hXE₂⟩ :=
      exists_isHallPiSubgroupOf_ge_of_isPiSubgroup (X := U) (U := X) hUsolv hXU hXpi
    have hE₂ab : IsMulCommutative ↥E₂ :=
      FBG_tau_two_hall_abelian h₁ h₂ h₄ h₅ h₆ h₇ h₈ G hG2 M hM U hsemi E₂ hE₂hall
    have hE₂in : _root_.CFSG.FeitThompson.Prep06.IsHallPiIn (tauTwoPrimes M) E₂ U := by
      refine ⟨hE₂hall.1, fun s hs => ?_, fun s hs => ?_⟩
      · exact (isHallPiSubgroup_iff.1 hE₂hall.2).1 s
          (by rw [natCard_subgroupOf_of_le_aux hE₂hall.1]; exact hs)
      · exact (isHallPiSubgroup_iff.1 hE₂hall.2).2 s hs
    obtain ⟨hCle, huniq⟩ := FTS_abelian_rank_two_hall_centralizer_uniqueness h₃ G hG6 M U E₂
      hM hUM hsup hinf hE₂hall.1 hE₂ab hE₂in X hXE₂ hXbot hXc
    exact ⟨hCle, fun T hT hTle => huniq.eq_of_isCoatom hT hTle⟩

end

end CFSG.FeitThompson.Proofs
