module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.TauOneNarrowNormalizerDerivedExclusion
import CFSG.FeitThompson.Local.BetaCoreHallQuotient
import CFSG.FeitThompson.Local.CommonSylowNormalizerBetaFactor
import CFSG.FeitThompson.Local.NilpotentDerivedQuotientSylowNormalizer
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
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

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson

universe u

variable {G : Type u} [Group G]

theorem commutator_inf_le_sigmaCore [Finite G] (M L : Subgroup G) :
    ⁅sigmaCore M ⊓ L, M ⊓ L⁆ ≤ sigmaCore M :=
  (Subgroup.commutator_mono inf_le_left inf_le_left).trans
    (Subgroup.le_normalizer_iff_commutator_le_left.1 (le_normalizer_sigmaCore M))

theorem sup_inf_normalizer_eq_of_key {D L Y : Subgroup G} (hDL : D ≤ L) (hYL : Y ≤ L)
    (hkey : D.subgroupOf L ⊔ normalizer ((Y.subgroupOf L : Subgroup ↥L) : Set ↥L) = ⊤) :
    D ⊔ (normalizer (Y : Set G) ⊓ L) = L := by
  have hmap := congrArg (fun K : Subgroup ↥L => K.map L.subtype) hkey
  simp only [Subgroup.map_sup] at hmap
  rw [Subgroup.map_subgroupOf_eq_of_le hDL, ← Subgroup.subgroupOf_normalizer_eq hYL,
    Subgroup.subgroupOf_map_subtype] at hmap
  have htop : (⊤ : Subgroup ↥L).map L.subtype = L := by ext x; simp
  rw [htop] at hmap
  exact hmap

theorem dvd_natCard_sigmaCore_of_isHallPiSubgroup_subgroupOf [Finite G] {L : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hHall : IsHallPiSubgroup (sigmaPrimes L) ((sigmaCore L).subgroupOf L))
    (hpσ : p ∈ sigmaPrimes L) : p ∣ Nat.card ↥(sigmaCore L) := by
  have hmul := Subgroup.card_mul_index ((sigmaCore L).subgroupOf L)
  have hidx : ¬ p ∣ ((sigmaCore L).subgroupOf L).index := fun hd =>
    hHall.notMem_of_mem_primeFactors_index p
      (Nat.mem_primeFactors.2 ⟨hp, hd, Subgroup.index_ne_zero_of_finite⟩) hpσ
  have hpL : p ∣ Nat.card ↥L := dvd_natCard_of_mem_sigmaPrimes hpσ
  rw [← hmul] at hpL
  have h := (hp.dvd_mul.1 hpL).resolve_right hidx
  rwa [natCard_subgroupOf_of_le (sigmaCore_le L)] at h

theorem mem_betaPrimes_of_commutator_ne_bot [Finite G]
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_beta_prime_centralizing_sylow.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    (hG : Prep08.IsMinimalSimpleOddOrder G) {M E L : Subgroup G} {p : ℕ}
    (hM : IsCoatom M) (hEM : E ≤ M)
    (hE : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E)
    (hL : IsCoatom L) (hpτ : p ∈ tau1Primes M) (hpσL : p ∈ sigmaPrimes L)
    (hC : ⁅sigmaCore M ⊓ L, M ⊓ L⁆ ≠ ⊥) : p ∈ betaPrimes G := by
  have hp : p.Prime := prime_of_mem_tau1Primes hpτ
  have : Fintype G := Fintype.ofFinite G
  have hG02 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG06 : Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG09 : Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  by_contra hpβ
  have hpβL : p ∉ betaPrimes ↥L := fun h =>
    hpβ ((mem_betaPrimes_subgroup_iff_of_mem_sigmaPrimes hpσL).1 h)
  obtain ⟨q, hq, hqC⟩ := Nat.exists_prime_and_dvd
    (n := Nat.card ↥(⁅sigmaCore M ⊓ L, M ⊓ L⁆ : Subgroup G))
    (fun h => hC (Subgroup.card_eq_one.1 h))
  have hqσM : q ∈ sigmaPrimes M :=
    isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) q (Nat.mem_primeFactors.2
      ⟨hq, hqC.trans (Subgroup.card_dvd_of_le (commutator_inf_le_sigmaCore M L)),
        Nat.card_pos.ne'⟩)
  have hqL' : q ∣ Nat.card (⁅L, L⁆ : Subgroup G) :=
    hqC.trans (Subgroup.card_dvd_of_le (Subgroup.commutator_mono inf_le_right inf_le_right))
  obtain ⟨-, -, -, hBL', -, hNnil, hnil⟩ := FTS_beta_core_hall_quotient h₁ h₈ G hG06 L hL
  have := Fact.mk hq
  obtain ⟨Q⟩ := (Sylow.nonempty : Nonempty (Sylow q ↥(⁅L, L⁆ : Subgroup G)))
  set Y : Subgroup G :=
    (Q : Subgroup ↥(⁅L, L⁆ : Subgroup G)).map (⁅L, L⁆ : Subgroup G).subtype with hYdef
  have hYL' : Y ≤ (⁅L, L⁆ : Subgroup G) := Subgroup.map_subtype_le _
  have hYcard : Nat.card ↥Y = q ^ (Nat.card ↥(⁅L, L⁆ : Subgroup G)).factorization q := by
    rw [hYdef, Subgroup.card_subtype, Q.card_eq_multiplicity]
  have hYq : IsPGroup q ↥Y := Q.isPGroup'.map _
  have hYne : Y ≠ ⊥ := by
    intro h
    have hfac : 0 < (Nat.card ↥(⁅L, L⁆ : Subgroup G)).factorization q :=
      hq.factorization_pos_of_dvd Nat.card_pos.ne' hqL'
    rw [h, Subgroup.card_bot] at hYcard
    have h1 : 1 < q ^ (Nat.card ↥(⁅L, L⁆ : Subgroup G)).factorization q :=
      Nat.one_lt_pow hfac.ne' hq.one_lt
    omega
  have hLL : (⁅L, L⁆ : Subgroup G) ≤ L := Subgroup.commutator_le_self L
  have hYLle : Y ≤ L := hYL'.trans hLL
  have := betaCore_normal_subgroupOf L
  have := normal_subgroupOf_commutator_self L
  have hnormBB := normal_subgroupOf_subgroupOf (M := L) hLL hNnil
  have := hnormBB
  have hnil2 := isNilpotent_quotient_subgroupOf_subgroupOf (M := L) (A := betaCore L)
    (B := (⁅L, L⁆ : Subgroup G)) hLL hnil
  have hYcard2 : Nat.card ↥(Y.subgroupOf L)
      = q ^ (Nat.card ↥((⁅L, L⁆ : Subgroup G).subgroupOf L)).factorization q := by
    rw [natCard_subgroupOf_of_le hYLle, natCard_subgroupOf_of_le hLL, hYcard]
  have hkey := sup_normalizer_eq_top_of_isNilpotent_quotient (X := ↥L)
    (B := (betaCore L).subgroupOf L) (Y := Y.subgroupOf L)
    (L := (⁅L, L⁆ : Subgroup G).subgroupOf L) hq (Subgroup.comap_mono hBL') hnil2
    (Subgroup.comap_mono hYL') hYcard2
  have hsup : betaCore L ⊔ (normalizer (Y : Set G) ⊓ L) = L :=
    sup_inf_normalizer_eq_of_key (betaCore_le L) hYLle hkey
  have hpD : ¬ p ∣ Nat.card ↥(betaCore L) := fun hd =>
    hpβL (isPiSubgroup_iff.1 (isPiSubgroup_betaCore L) p
      (Nat.mem_primeFactors.2 ⟨hp, hd, Nat.card_pos.ne'⟩))
  have hpN : ¬ p ∣ Nat.card
      (⁅normalizer (Y : Set G), normalizer (Y : Set G)⁆ : Subgroup G) :=
    FTS_tau_one_narrow_normalizer_derived_exclusion h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ G hG09 M hM E hEM
      hE p hpτ hpβ q hqσM Y hYne hYq
  have hpJ : ¬ p ∣ Nat.card
      (⁅normalizer (Y : Set G) ⊓ L, normalizer (Y : Set G) ⊓ L⁆ : Subgroup G) := fun hd =>
    hpN (hd.trans (Subgroup.card_dvd_of_le
      (Subgroup.commutator_mono inf_le_left inf_le_left)))
  have hpL' : ¬ p ∣ Nat.card (⁅L, L⁆ : Subgroup G) :=
    not_dvd_natCard_commutator_of_sup_eq hp (betaCore_le L) inf_le_right
      (betaCore_normal_subgroupOf L) hsup hpD hpJ
  obtain ⟨hHallOfL, -, hSL⟩ := h₁ G hG02 L hL
  exact hpL' ((dvd_natCard_sigmaCore_of_isHallPiSubgroup_subgroupOf hp hHallOfL.2 hpσL).trans
    (Subgroup.card_dvd_of_le hSL))

theorem FTS_nonconjugate_intersection_tau_one_beta
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_beta_prime_centralizing_sylow.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_nonconjugate_intersection_tau_one_beta.{u} := by
  intro G _ _ hG M E L p hM hEM hE hL _hLM hpτ hpσL hC
  have hβG := mem_betaPrimes_of_commutator_ne_bot h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ hG hM hEM hE hL
    hpτ hpσL hC
  exact ⟨hβG, (mem_betaPrimes_subgroup_iff_of_mem_sigmaPrimes hpσL).2 hβG⟩

end

end CFSG.FeitThompson.Proofs
