module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.ResidualNormalizerSingleRankTwoPrime
import CFSG.FeitThompson.Local.KappaResidualContainedOppositeSigmaCore
import CFSG.FeitThompson.Local.MaximalTauTwoNonemptyTypeIOrII
import CFSG.FeitThompson.Local.NonuniqueScnAuxiliaryPrime
import CFSG.FeitThompson.Local.MaximalInvariantSubgroupTransport
import CFSG.FeitThompson.Local.MaximalIntersectionSylowNormalizerControl
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

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
open Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem isPlaneAt_of_mulEquiv {p : ℕ} {B : Subgroup G} {G' : Type*} [Group G'] {B' : Subgroup G'}
    (e : ↥B ≃* ↥B') (h : Prep08.IsPlaneAt p B) : Prep08.IsPlaneAt p B' := by
  obtain ⟨hea, hcard⟩ := h
  rw [isElementaryAbelian_iff] at hea
  refine ⟨isElementaryAbelian_iff.2 ⟨?_, ?_⟩, ?_⟩
  · refine IsMulCommutative.of_comm fun a b => e.symm.injective ?_
    rw [map_mul, map_mul]
    exact hea.1.is_comm.comm _ _
  · intro x hx
    have hy : (e.symm ⟨x, hx⟩ : ↥B) ^ p = 1 :=
      Subtype.ext (by simpa using hea.2 _ (e.symm ⟨x, hx⟩).2)
    have hx' : (⟨x, hx⟩ : ↥B') ^ p = 1 := by simpa using congrArg e hy
    exact congrArg (Subgroup.subtype B') hx'
  · rw [← Nat.card_congr e.toEquiv, hcard]

omit [Finite G] in
theorem isPlaneAt_map {p : ℕ} {B : Subgroup G} {G' : Type*} [Group G'] (f : G →* G')
    (hf : Function.Injective f) (h : Prep08.IsPlaneAt p B) : Prep08.IsPlaneAt p (B.map f) :=
  isPlaneAt_of_mulEquiv (B.equivMapOfInjective f hf) h

omit [Finite G] in
theorem isPlaneAt_of_mulEquiv_pi {p : ℕ} {B : Subgroup G}
    (e : ↥B ≃* (Fin 2 → Multiplicative (ZMod p))) : Prep08.IsPlaneAt p B := by
  refine ⟨isElementaryAbelian_iff.2 ⟨?_, fun x hx => ?_⟩, ?_⟩
  · exact IsMulCommutative.of_comm fun a b => e.injective (by rw [map_mul, map_mul, mul_comm])
  · exact congrArg (Subgroup.subtype B)
      (e.injective (a₁ := (⟨x, hx⟩ : ↥B) ^ p) (a₂ := 1)
        (by rw [map_pow, pow_eq_one_pi_multiplicative_zmod, map_one]))
  · rw [Nat.card_congr e.toEquiv, card_pi_multiplicative_zmod]

omit [Finite G] in
theorem nonempty_mulEquiv_of_isPlaneAt {p : ℕ} (hp : p.Prime) {B : Subgroup G}
    (h : Prep08.IsPlaneAt p B) : Nonempty (↥B ≃* (Fin 2 → Multiplicative (ZMod p))) := by
  obtain ⟨hea, hcard⟩ := h
  rw [isElementaryAbelian_iff] at hea
  have : IsMulCommutative ↥B := hea.1
  let _ : CommGroup ↥B := IsMulCommutative.instCommGroup
  exact nonempty_mulEquiv_pi_of_exponent hp (fun x => Subtype.ext (hea.2 x.1 x.2)) hcard

theorem exists_isPlaneAt_le_of_two_le_elementaryAbelianPRank {p : ℕ} (hp : p.Prime)
    {M U : Subgroup G} (hUM : U ≤ M) (hidx : ¬ p ∣ U.relIndex M)
    (hrank : 2 ≤ elementaryAbelianPRank p ↥M) :
    ∃ B : Subgroup G, B ≤ U ∧ Prep08.IsPlaneAt p B := by
  have _inst : Fact p.Prime := ⟨hp⟩
  set V : Subgroup ↥M := U.subgroupOf M with hV
  have hidxV : ¬ p ∣ V.index := hidx
  have h1 : V.index * Nat.card ↥V = Nat.card ↥M := Subgroup.index_mul_card V
  have h2 : V.index ≠ 0 := by
    intro h
    rw [h, zero_mul] at h1
    exact Nat.card_pos.ne' h1.symm
  have hfac : (Nat.card ↥V).factorization p = (Nat.card ↥M).factorization p := by
    have h3 : (V.index).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hidxV
    have h4 := congrArg (fun n => n.factorization p) h1
    simp only [Nat.factorization_mul h2 Nat.card_pos.ne', Finsupp.add_apply, h3, zero_add] at h4
    exact h4
  obtain ⟨T, -, hTV, hTcard⟩ :=
    exists_le_natCard_eq_pow_factorization (G := ↥M) hp (H := V) (R := ⊥) bot_le IsPGroup.of_bot
  rw [hfac] at hTcard
  obtain ⟨A', ⟨e⟩⟩ := mem_elementaryAbelianRanks.1
    ((le_elementaryAbelianPRank_iff (M := ↥M) hp.one_lt).1 hrank)
  have hA'rank : 2 ≤ elementaryAbelianPRank p ↥A' :=
    le_elementaryAbelianPRank hp.one_lt
      (mem_elementaryAbelianRanks.2 ⟨⊤, ⟨Subgroup.topEquiv.trans e⟩⟩)
  have hA'p : IsPGroup p ↥A' := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_congr e.toEquiv, card_pi_multiplicative_zmod]
  obtain ⟨g, hg⟩ := exists_le_conj_smul_of_isPGroup (P := T) hTcard hA'p
  have hTrank : 2 ≤ elementaryAbelianPRank p ↥T := by
    calc 2 ≤ elementaryAbelianPRank p ↥A' := hA'rank
      _ ≤ elementaryAbelianPRank p ↥(MulAut.conj g • T) :=
          elementaryAbelianPRank_le_of_le hp.one_lt hg
      _ = elementaryAbelianPRank p ↥T := elementaryAbelianPRank_conj_smul hp.one_lt g T
  obtain ⟨W, ⟨eW⟩⟩ := mem_elementaryAbelianRanks.1
    ((le_elementaryAbelianPRank_iff (M := ↥T) hp.one_lt).1 hTrank)
  have hWV : W.map T.subtype ≤ V := le_trans (Subgroup.map_subtype_le _) hTV
  refine ⟨((W.map T.subtype).map M.subtype), ?_, ?_⟩
  · have := Subgroup.map_mono (f := M.subtype) hWV
    rwa [hV, Subgroup.map_subgroupOf_eq_of_le hUM] at this
  · exact isPlaneAt_map M.subtype M.subtype_injective
      (isPlaneAt_map T.subtype T.subtype_injective (isPlaneAt_of_mulEquiv_pi eW))

theorem not_dvd_relIndex_of_mem_tauTwoPrimes {p : ℕ} {M U : Subgroup G}
    (hU : Prep08.IsHallOf {s : ℕ | s.Prime ∧ s ∉ sigmaPrimes M ∧ s ∉ kappaPrimes M} U M)
    (h : p ∈ tauTwoPrimes M) : ¬ p ∣ U.relIndex M := by
  obtain ⟨-, hHall⟩ := hU
  rw [isHallPiSubgroup_iff] at hHall
  intro hdvd
  refine hHall.2 p ?_ ⟨prime_of_mem_tauTwoPrimes h,
    notMem_sigmaPrimes_of_mem_tauTwoPrimes h, notMem_kappaPrimes_of_mem_tauTwoPrimes h⟩
  exact Nat.mem_primeFactors.2
    ⟨prime_of_mem_tauTwoPrimes h, hdvd, Subgroup.index_ne_zero_of_finite⟩

theorem exists_isPlaneAt_le_of_mem_tauTwoPrimes {p : ℕ} {M U : Subgroup G}
    (hU : Prep08.IsHallOf {s : ℕ | s.Prime ∧ s ∉ sigmaPrimes M ∧ s ∉ kappaPrimes M} U M)
    (h : p ∈ tauTwoPrimes M) : ∃ B : Subgroup G, B ≤ U ∧ Prep08.IsPlaneAt p B :=
  exists_isPlaneAt_le_of_two_le_elementaryAbelianPRank (prime_of_mem_tauTwoPrimes h) hU.le
    (not_dvd_relIndex_of_mem_tauTwoPrimes hU h)
    (elementaryAbelianPRank_eq_two_of_mem_tauTwoPrimes h).ge

theorem not_dvd_index_subgroupOf_of_isHallKappa {M K : Subgroup G} (hq : (Nat.card ↥K).Prime)
    (hK : Prep08.IsHallOf (kappaPrimes M) K M) : ¬ Nat.card ↥K ∣ (K.subgroupOf M).index := by
  obtain ⟨hKM, hHall⟩ := hK
  rw [isHallPiSubgroup_iff] at hHall
  have hcard : Nat.card ↥(K.subgroupOf M) = Nat.card ↥K :=
    Nat.card_congr (subgroupOfEquivOfLe hKM).toEquiv
  have hmem : Nat.card ↥K ∈ kappaPrimes M := by
    refine hHall.1 _ ?_
    rw [hcard]
    exact Nat.mem_primeFactors.2 ⟨hq, dvd_rfl, hq.ne_zero⟩
  exact fun hdvd => hHall.2 _
    (Nat.mem_primeFactors.2 ⟨hq, hdvd, Subgroup.index_ne_zero_of_finite⟩) hmem

theorem isKappaResidualPartner_of_isKappaResidualSetup {M K U A Mstar R H : Subgroup G} {r : ℕ}
    (h : Prep08.IsKappaResidualSetup M K U A Mstar R H r) :
    IsKappaResidualPartner r M K U A Mstar R H where
  config :=
    { isCoatom := h.isCoatom_M
      kappaPrimes_nonempty := h.kappa_nonempty
      isHallKappa := ⟨h.isHall_K.1, h.isHall_K.2⟩
      isHallCompl := ⟨h.isHall_U.1, h.isHall_U.2⟩
      isInternalSemidirectProduct := h.semidirect_M
      isInternalSemidirectProduct_complement := h.semidirect_UK }
  isMulCommutative_U := h.isMulCommutative_U
  centralizer_eq_bot := h.centralizer_U
  U_ne_bot := h.U_ne_bot
  A_eq := h.A_eq
  isCoatom_Mstar := h.isCoatom_Mstar
  exists_prime_order_normalizer_le := h.exists_prime_order_le_K
  prime_r := h.prime_r
  dvd_natCard_U := h.r_dvd
  isSylowSubgroupOf_R :=
    ⟨h.isSylow_R.le, (Prep08.isSylowOf_iff_natCard h.prime_r h.isSylow_R.le).1 h.isSylow_R⟩
  isCoatom_H := h.isCoatom_H
  normalizer_R_le := h.normalizer_R_le

theorem centralizer_le_of_kappa_local_pair
    (h₁ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_local_pair.{u})
    (hG : Prep08.IsMinimalSimpleOddOrder G) {M K U A Mstar R H : Subgroup G} {r : ℕ}
    (hsetup : Prep08.IsKappaResidualSetup M K U A Mstar R H r)
    (hq : (Nat.card ↥K).Prime) :
    centralizer ((K : Subgroup G) : Set G) ≤ Mstar := by
  have _inst : Fintype G := Fintype.ofFinite G
  have hkappa : Prep03.IsKappaSetup G M K (sigmaCore M ⊓ centralizer ((K : Subgroup G) : Set G))
      (K ⊔ (sigmaCore M ⊓ centralizer ((K : Subgroup G) : Set G))) :=
    { ambient := ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative,
        hG.isSolvable_of_ne_top⟩
      isCoatom := hsetup.isCoatom_M
      kappa_nonempty := hsetup.kappa_nonempty
      isHall_K := by
        obtain ⟨hKM, hHall⟩ := hsetup.isHall_K
        rw [isHallPiSubgroup_iff] at hHall
        refine ⟨hKM, fun s hs => hHall.1 s ?_, fun s hs => hHall.2 s hs⟩
        rwa [Nat.card_congr (subgroupOfEquivOfLe hKM).toEquiv]
      A_eq := rfl
      Z_eq := rfl }
  obtain ⟨Mstar', -, huniq, -, -, -, -, -, -, -, -, hprime, -, -⟩ := h₁ G M K _ _ hkappa
  have hMstar : Mstar = Mstar' :=
    huniq Mstar hsetup.isCoatom_Mstar hsetup.exists_prime_order_le_K
  rw [hMstar]
  exact (hprime K le_rfl hq).2.1

theorem not_centralizer_le_of_kappa_residual
    (h₁ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_local_pair.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_nonabelian_ambient_unique_nonregular_line.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_residual_containing_complement_fitting.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_residual_partner_intersection_complement.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_residual_prime_overgroup_position.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_residual_partner_nilpotent_nonabelian_sylow.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FTS_residual_rank_two_plane_partner_fitting.{u})
    (hG : Prep08.IsMinimalSimpleOddOrder G) {M K U A Mstar R H : Subgroup G} {r : ℕ}
    (hsetup : Prep08.IsKappaResidualSetup M K U A Mstar R H r)
    (hne : (tauTwoPrimes H).Nonempty) :
    ¬ centralizer ((U : Subgroup G) : Set G) ≤ M := by
  have hamb : IsFTAmbient G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hG4 : IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hpartner := isKappaResidualPartner_of_isKappaResidualSetup hsetup
  obtain ⟨hq, -, -, hHMstar, -, -⟩ := h₆ G hG M K U A Mstar R H r hsetup
  obtain ⟨-, hsingle, -, -⟩ :=
    FTS_residual_normalizer_single_rank_two_prime h₃ h₆ h₉ G hG M K U A Mstar R H r hsetup hne
  set q : ℕ := Nat.card ↥K with hqdef
  have hqmem : q ∈ tauTwoPrimes H := by rw [hsingle]; rfl
  obtain ⟨hmain, hexists⟩ := h₉ G hG M K U A Mstar R H r hsetup hne
  obtain ⟨B, hBle, hBplane⟩ := hexists q hqmem
  obtain ⟨-, hBK, -, -, -, -, -⟩ := hmain q hqmem B hBle hBplane
  obtain ⟨hsemiH, -⟩ := h₅ G hamb r M K U A Mstar R H hpartner
  obtain ⟨-, -, -, hQnonab, -, -, hQtop⟩ := h₈ G hG M K U A Mstar R H r hsetup hne
  have hUSH : U ≤ sigmaCore H :=
    FTS_kappa_residual_contained_opposite_sigma_core h₄ h₆ G hamb r M K U A Mstar R H hpartner
  have hplanePacket : IsOutsideSigmaPlane q H B :=
    { isCoatom := hsetup.isCoatom_H
      prime := hq
      notMem_sigmaPrimes := notMem_sigmaPrimes_of_mem_tauTwoPrimes hqmem
      le := le_trans hBle inf_le_left
      isElementaryAbelianPlane := nonempty_mulEquiv_of_isPlaneAt hq hBplane }
  have hcompl : IsSigmaComplement H (H ⊓ Mstar) :=
    { isCoatom := hsetup.isCoatom_H
      isInternalSemidirectProduct := hsemiH }
  have hnonabSylow : ∃ P : Subgroup G, IsSylowSubgroup q P ∧ ¬ IsMulCommutative ↥P := by
    refine ⟨Prep08.pCoreOfSubgroup q Mstar, ?_, hQnonab⟩
    obtain ⟨S, hS⟩ := (Prep08.isSylowOf_top_iff hq).1 hQtop
    exact ⟨S, hS⟩
  obtain ⟨A0, hA0B, hA0card, hA0cent, -, -, -, -⟩ :=
    h₂ G hG4 q H B (H ⊓ Mstar) hplanePacket hcompl hBle hnonabSylow
  have hA0K : A0 ≠ K := by
    intro hEq
    have hSHC : sigmaCore H ≤ centralizer ((K : Subgroup G) : Set G) := by
      rw [← hEq]
      exact hA0cent.ge.trans inf_le_right
    have hSHMstar : sigmaCore H ≤ Mstar :=
      hSHC.trans (centralizer_le_of_kappa_local_pair h₁ hG hsetup hq)
    have hHMstar' : H ≤ Mstar := by
      rw [← hsemiH.sup_eq]
      exact sup_le hSHMstar inf_le_right
    have hHeq : H = Mstar := by
      rcases eq_or_lt_of_le hHMstar' with h | h
      · exact h
      · exact absurd (hsetup.isCoatom_H.2 Mstar h) hsetup.isCoatom_Mstar.1
    exact hHMstar 1 (by simpa using hHeq)
  have hA0M : ¬ A0 ≤ M := by
    intro hA0M
    have hBC : B ≤ centralizer ((K : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hBK
    have hA0N : A0 ≤ normalizer ((K : Subgroup G) : Set G) :=
      (hA0B.trans hBC).trans (Subgroup.centralizer_le_normalizer _)
    have hKp : IsPGroup q ↥K := IsPGroup.of_card (n := 1) (by rw [pow_one])
    have hA0p : IsPGroup q ↥A0 := IsPGroup.of_card (n := 1) (by rw [pow_one, hA0card])
    have hsupp : IsPGroup q ↥(K ⊔ A0) := IsPGroup.to_sup_of_normal_left' hKp hA0p hA0N
    have hKM : K ≤ M := hsetup.isHall_K.le
    have hidx := not_dvd_index_subgroupOf_of_isHallKappa hq hsetup.isHall_K
    have hle : K ⊔ A0 ≤ K :=
      le_of_isPGroup_of_not_dvd_index hq (sup_le hKM hA0M) hKp hsupp hidx le_sup_left
    exact hA0K (Subgroup.eq_of_le_of_card_ge (le_trans le_sup_right hle) (by rw [hA0card]))
  intro hCU
  refine hA0M (le_trans ?_ hCU)
  intro x hx
  refine mem_centralizer_iff.2 fun y hy => ?_
  have hyC : y ∈ centralizer ((A0 : Subgroup G) : Set G) := (hA0cent.ge (hUSH hy)).2
  exact (mem_centralizer_iff.1 hyC x hx).symm

theorem FTS_kappa_residual_rank_two_exclusion
    (h₁ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_local_pair.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_nonabelian_ambient_unique_nonregular_line.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_residual_containing_complement_fitting.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_residual_partner_intersection_complement.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_residual_prime_overgroup_position.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_residual_partner_nilpotent_nonabelian_sylow.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FTS_residual_rank_two_plane_partner_fitting.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_kappa_residual_rank_two_exclusion.{u} := by
  intro G _ _ hG M K U A Mstar R H r hsetup hne
  have hq : (Nat.card ↥K).Prime := (h₆ G hG M K U A Mstar R H r hsetup).1
  obtain ⟨-, hsingle, -, -⟩ :=
    FTS_residual_normalizer_single_rank_two_prime h₃ h₆ h₉ G hG M K U A Mstar R H r hsetup hne
  have hCU : ¬ centralizer ((U : Subgroup G) : Set G) ≤ M :=
    not_centralizer_le_of_kappa_residual h₁ h₂ h₃ h₄ h₅ h₆ h₈ h₉ hG hsetup hne
  refine ⟨hq, hsingle, ?_, hCU⟩
  refine Set.eq_empty_iff_forall_notMem.2 fun p hp => hCU ?_
  obtain ⟨B0, hB0U, hB0plane⟩ := exists_isPlaneAt_le_of_mem_tauTwoPrimes hsetup.isHall_U hp
  have hB0M : B0 ≤ M := hB0U.trans hsetup.isHall_U.le
  obtain ⟨hCB0, -⟩ :=
    h₇ G hG M B0 p hsetup.isCoatom_M (prime_of_mem_tauTwoPrimes hp) hB0M hB0plane
  exact le_trans (Subgroup.centralizer_le hB0U) hCB0

end

end CFSG.FeitThompson.Proofs
