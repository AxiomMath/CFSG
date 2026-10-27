module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.OutsideSigmaKappaSylowCoreNilpotent
import CFSG.FeitThompson.Local.SharedSigmaSylowSetup
import CFSG.FeitThompson.Local.NormalProductCoprimeNormalizerFactorization
import Mathlib.Tactic.Group
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

theorem mem_normalizer_subgroupOf_iff {M U : Subgroup G} (hUM : U ≤ M) (x : ↥M) :
    x ∈ normalizer ((U.subgroupOf M : Subgroup ↥M) : Set ↥M) ↔
      (x : G) ∈ normalizer (U : Set G) := by
  simp only [Subgroup.mem_normalizer_iff]
  refine ⟨fun h g => ⟨fun hg => ?_, fun hg => ?_⟩, fun h n => ?_⟩
  · have := (h ⟨g, hUM hg⟩).1 ((Subgroup.mem_subgroupOf).2 hg)
    simpa [Subgroup.mem_subgroupOf] using this
  · have hgM : g ∈ M := by
      have h1 : (x : G) * g * (x : G)⁻¹ ∈ M := hUM hg
      have h2 : g = (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * (x : G) := by group
      rw [h2]
      exact M.mul_mem (M.mul_mem (M.inv_mem x.2) h1) x.2
    have := (h ⟨g, hgM⟩).2 ((Subgroup.mem_subgroupOf).2 hg)
    simpa [Subgroup.mem_subgroupOf] using this
  · simpa [Subgroup.mem_subgroupOf] using h (n : G)

theorem mem_centralizer_subgroupOf_iff {M U : Subgroup G} (hUM : U ≤ M) (x : ↥M) :
    x ∈ centralizer ((U.subgroupOf M : Subgroup ↥M) : Set ↥M) ↔
      (x : G) ∈ centralizer (U : Set G) := by
  simp only [Subgroup.mem_centralizer_iff]
  exact ⟨fun h g hg => congrArg Subtype.val
      (h (⟨g, hUM hg⟩ : ↥M) ((Subgroup.mem_subgroupOf).2 hg)),
    fun h n hn => Subtype.ext (h (n : G) ((Subgroup.mem_subgroupOf).1 hn))⟩

section

open CFSG.FeitThompson

theorem exists_isSylowSubgroupOf_le [Finite G] {M U : Subgroup G} {r : ℕ} (hr : r.Prime)
    (hU : IsHallPiSubgroupOf {q : ℕ | q.Prime ∧ q ∉ sigmaPrimes M ∧ q ∉ kappaPrimes M} U M)
    (hrU : r ∣ Nat.card ↥U) :
    ∃ R : Subgroup G, R ≤ U ∧ _root_.CFSG.FeitThompson.IsSylowIn r M R := by
  have := Fact.mk hr
  have hrπ : r ∈ {q : ℕ | q.Prime ∧ q ∉ sigmaPrimes M ∧ q ∉ kappaPrimes M} :=
    isPiSubgroup_iff.1 hU.isPiSubgroup r (Nat.mem_primeFactors.2 ⟨hr, hrU, Nat.card_pos.ne'⟩)
  obtain ⟨S⟩ : Nonempty (Sylow r ↥U) := inferInstance
  refine ⟨(S : Subgroup ↥U).map U.subtype, Subgroup.map_subtype_le _, ?_⟩
  rw [_root_.CFSG.FeitThompson.isSylowIn_iff_natCard hr
      ((Subgroup.map_subtype_le _).trans hU.le),
    Subgroup.card_subtype, S.card_eq_multiplicity,
    factorization_natCard_eq_of_isHallPiSubgroupOf hU hr hrπ]

theorem coprime_natCard_sigmaCore_of_isHallPiSubgroupOf [Finite G] {M U : Subgroup G}
    (hU : IsHallPiSubgroupOf {q : ℕ | q.Prime ∧ q ∉ sigmaPrimes M ∧ q ∉ kappaPrimes M} U M) :
    Nat.Coprime (Nat.card ↥(sigmaCore M)) (Nat.card ↥U) := by
  refine (Nat.disjoint_primeFactors Nat.card_pos.ne' Nat.card_pos.ne').1
    (Finset.disjoint_left.2 fun q hq hq' => ?_)
  exact (isPiSubgroup_iff.1 hU.isPiSubgroup q hq').2.1
    (isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) q hq)

theorem inf_centralizer_eq_bot_of_isKappaResidualConfig [Finite G]
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (hG : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G) {M K U : Subgroup G}
    (hcfg : IsKappaResidualConfig M K U) (hUbot : U ≠ ⊥) :
    sigmaCore M ⊓ centralizer (U : Set G) = ⊥ := by
  have hone : Nat.card ↥U ≠ 1 := fun h => hUbot (Subgroup.card_eq_one.1 h)
  obtain ⟨r, hr, hrU⟩ := Nat.exists_prime_and_dvd hone
  obtain ⟨R, hRU, hR⟩ := exists_isSylowSubgroupOf_le hr hcfg.isHallCompl hrU
  have hrπ : r ∈ {q : ℕ | q.Prime ∧ q ∉ sigmaPrimes M ∧ q ∉ kappaPrimes M} :=
    isPiSubgroup_iff.1 hcfg.isHallCompl.isPiSubgroup r
      (Nat.mem_primeFactors.2 ⟨hr, hrU, Nat.card_pos.ne'⟩)
  have hrM : r ∣ Nat.card ↥M := hrU.trans (Subgroup.card_dvd_of_le hcfg.isHallCompl.le)
  obtain ⟨-, ⟨A, hAset, -, -, hAC⟩, -⟩ :=
    _root_.CFSG.FeitThompson.Proofs.sylow_outside_sigma_kappa h₂ h₃ hG hcfg.isCoatom hr hrM
      hrπ.2.1 hrπ.2.2 hR
  have hAU : A ≤ U := fun x hx => hRU (hAset ▸ hx : x ∈ {y ∈ (R : Set G) | y ^ r = 1}).1
  exact le_bot_iff.1 ((inf_le_inf_left _ (Subgroup.centralizer_le hAU)).trans hAC.le)

theorem normalizer_inf_eq_of_inf_centralizer_eq_bot [Finite G] {M K U : Subgroup G}
    (hsolv : Group.IsSolvable ↥M) (hcfg : IsKappaResidualConfig M K U)
    (hC : sigmaCore M ⊓ centralizer (U : Set G) = ⊥) :
    normalizer (U : Set G) ⊓ M = U ⊔ K := by
  have := hsolv
  have hUM : U ≤ M := hcfg.isHallCompl.le
  have hUKM : U ⊔ K ≤ M := hcfg.isInternalSemidirectProduct.right_le
  have hSM : sigmaCore M ≤ M := sigmaCore_le M
  have hDJ : (sigmaCore M).subgroupOf M ⊔ (U ⊔ K).subgroupOf M = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hSM hUKM,
      hcfg.isInternalSemidirectProduct.sup_eq, Subgroup.subgroupOf_self]
  have hU'J : U.subgroupOf M ≤ (U ⊔ K).subgroupOf M := Subgroup.comap_mono le_sup_left
  have hcop : Nat.Coprime (Nat.card ↥((sigmaCore M).subgroupOf M))
      (Nat.card ↥(U.subgroupOf M)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv]
    exact coprime_natCard_sigmaCore_of_isHallPiSubgroupOf hcfg.isHallCompl
  have hDC : (sigmaCore M).subgroupOf M ⊓
      centralizer ((U.subgroupOf M : Subgroup ↥M) : Set ↥M) = ⊥ := by
    refine le_bot_iff.1 fun x hx => ?_
    obtain ⟨hxD, hxC⟩ := Subgroup.mem_inf.1 hx
    have hx1 : (x : G) = 1 := by
      rw [← Subgroup.mem_bot (G := G), ← hC]
      exact Subgroup.mem_inf.2
        ⟨(Subgroup.mem_subgroupOf).1 hxD, (mem_centralizer_subgroupOf_iff hUM x).1 hxC⟩
    exact Subgroup.mem_bot.2 (Subtype.ext hx1)
  have hJN : (U ⊔ K).subgroupOf M ≤ normalizer ((U.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
    intro x hx
    rw [mem_normalizer_subgroupOf_iff hUM]
    exact hcfg.isInternalSemidirectProduct_complement.le_normalizer
      ((Subgroup.mem_subgroupOf).1 hx)
  have hform := CFSG.FeitThompson.normalizer_eq_inf_centralizer_sup_inf_normalizer
    (D := (sigmaCore M).subgroupOf M) (J := (U ⊔ K).subgroupOf M) (U := U.subgroupOf M)
    hDJ hU'J hcop
  rw [hDC, inf_eq_left.2 hJN, bot_sup_eq] at hform
  refine le_antisymm (fun x hx => ?_) (le_inf ?_ hUKM)
  · obtain ⟨hxN, hxM⟩ := Subgroup.mem_inf.1 hx
    have h1 : (⟨x, hxM⟩ : ↥M) ∈ normalizer ((U.subgroupOf M : Subgroup ↥M) : Set ↥M) :=
      (mem_normalizer_subgroupOf_iff hUM ⟨x, hxM⟩).2 hxN
    rw [hform] at h1
    exact (Subgroup.mem_subgroupOf).1 h1
  · exact hcfg.isInternalSemidirectProduct_complement.le_normalizer

theorem kappa_residual_local_normalizer [Finite G]
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (hG : IsFTAmbient G) {M K U : Subgroup G}
    (hcfg : IsKappaResidualConfig M K U) (hUbot : U ≠ ⊥) :
    sigmaCore M ⊓ centralizer (U : Set G) = ⊥ ∧ normalizer (U : Set G) ⊓ M = U ⊔ K := by
  have hG04 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hC : sigmaCore M ⊓ centralizer (U : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_isKappaResidualConfig h₂ h₃ hG04 hcfg hUbot
  exact ⟨hC, normalizer_inf_eq_of_inf_centralizer_eq_bot
    (hG.isSolvable M hcfg.isCoatom.1) hcfg hC⟩

theorem FTS_kappa_residual_local_normalizer
    (_h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_kappa_residual_local_normalizer.{u} := by
  intro G _ _ hG M K U hcfg hUbot
  exact kappa_residual_local_normalizer h₂ h₃ hG hcfg hUbot

end

end

end CFSG.FeitThompson.Proofs
