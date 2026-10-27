module

public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.Local.OutsideSigmaCoreCentralizerRankOne
public import CFSG.FeitThompson.Local.FittingSplitsNormalHall
import CFSG.FeitThompson.Local.CentralProductPlaneCentralizer
import CFSG.FeitThompson.Local.ZGroupSubgroupQuotient
import CFSG.FeitThompson.Local.CriticalSubgroupFixedLine
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.Local.PrimeCentralizerComplementNoncentral
import CFSG.FeitThompson.Local.AbelianSylowNormalPrimeCentralizerFitting
import CFSG.FeitThompson.Local.CompetingMaximalFittingPrimeSupport
import CFSG.FeitThompson.Local.InvariantRankTwoFactorsFixedFreeCycle
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Foundations.FittingContainsCentralizerSolvable
public import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport
import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent
import CFSG.FeitThompson.Representations.DadeSignalizersCanonicalNormalHall
import CFSG.FeitThompson.Local.NonconjugateDerivedPrimeIntersectionCentral
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
import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem subgroupOf_map_subtype_self {M : Subgroup G} (N : Subgroup ↥M) :
    (N.map M.subtype).subgroupOf M = N :=
  Subgroup.comap_map_eq_self_of_injective M.subtype_injective _

omit [Finite G] in
theorem subgroupOf_le_centralizer_subgroupOf {A B M : Subgroup G}
    (h : A ≤ centralizer (B : Set G)) :
    A.subgroupOf M ≤ centralizer ((B.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 (h hx)) (g : G) hg)

omit [Finite G] in
theorem le_centralizer_sup {A B C : Subgroup G} (hA : C ≤ centralizer (A : Set G))
    (hB : C ≤ centralizer (B : Set G)) : C ≤ centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [← le_centralizer_iff]
  exact sup_le (le_centralizer_iff.1 hA) (le_centralizer_iff.1 hB)

theorem index_subgroupOf_fittingPiPart_compl (π : Set ℕ) (X : Type*) [Group X] [Finite X] :
    ((fittingPiPart πᶜ X).subgroupOf (fittingRaw X)).index = Nat.card ↥(fittingPiPart π X) := by
  have hdp : IsInternalDirectProduct (fittingRaw X) (fittingPiPart π X) (fittingPiPart πᶜ X) :=
    isInternalDirectProduct_of_sup_eq (fittingPiPart_sup_compl π X)
      (fittingPiPart_inf_compl π X) (commutator_fittingPiPart_compl π X)
  have h2 : Nat.card ↥((fittingPiPart πᶜ X).subgroupOf (fittingRaw X)) *
      ((fittingPiPart πᶜ X).subgroupOf (fittingRaw X)).index = Nat.card ↥(fittingRaw X) :=
    Subgroup.card_mul_index _
  rw [natCard_subgroupOf_of_le fittingPiPart_le_fittingRaw, hdp.card_eq_mul, mul_comm] at h2
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2

theorem le_fittingPiPart_of_le_fittingRaw {X : Type*} [Group X] [Finite X] {π : Set ℕ}
    {K : Subgroup X} (hKF : K ≤ fittingRaw X) (hK : IsPiSubgroup π K) :
    K ≤ fittingPiPart π X := by
  have hchar := characteristic_subgroupOf_fittingPiPart π X
  have hidx : ((fittingPiPart π X).subgroupOf (fittingRaw X)).index
      = Nat.card ↥(fittingPiPart πᶜ X) := by
    have h := index_subgroupOf_fittingPiPart_compl πᶜ X
    rwa [compl_compl] at h
  have hcop : (Nat.card ↥K).Coprime ((fittingPiPart π X).subgroupOf (fittingRaw X)).index := by
    rw [hidx]
    exact (isPiSubgroup_iff_isPiNumber.1 hK).coprime_of_compl
      (isPiSubgroup_iff_isPiNumber.1 (isPiSubgroup_fittingPiPart πᶜ X))
      Nat.card_pos.ne' Nat.card_pos.ne'
  have h1 : K.subgroupOf (fittingRaw X) ≤ (fittingPiPart π X).subgroupOf (fittingRaw X) :=
    le_of_coprime_natCard_index (by rwa [natCard_subgroupOf_of_le hKF])
  have h2 := Subgroup.map_mono (f := (fittingRaw X).subtype) h1
  rwa [Subgroup.map_subgroupOf_eq_of_le hKF,
    Subgroup.map_subgroupOf_eq_of_le fittingPiPart_le_fittingRaw] at h2

theorem isCyclic_of_isNilpotent_of_forall_elementaryAbelianPRank_le_one {X : Type*} [Group X]
    [Finite X] [Group.IsNilpotent X] (hodd : Odd (Nat.card X))
    (hrank : ∀ r : ℕ, elementaryAbelianPRank r X ≤ 1) : IsCyclic X := by
  rw [← isZGroup_iff_isCyclic_of_isNilpotent]
  refine ⟨fun r hr P => ?_⟩
  have hrf := Fact.mk hr
  rcases eq_or_ne (P : Subgroup X) ⊥ with hP | hP
  · rw [hP]; infer_instance
  · have hntriv : Nontrivial ↥(P : Subgroup X) := (Subgroup.nontrivial_iff_ne_bot _).2 hP
    obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq P.isPGroup'
    have hk1 : 1 < Nat.card ↥(P : Subgroup X) := Finite.one_lt_card
    have hdvd : r ∣ Nat.card X := by
      refine dvd_trans ?_ (P : Subgroup X).card_subgroup_dvd_card
      rw [hk]
      refine dvd_pow_self r ?_
      rintro rfl
      rw [hk] at hk1; simp at hk1
    exact isCyclic_of_elementaryAbelianPRank_le_one hr (hodd.of_dvd_nat hdvd) P.isPGroup'
      (le_trans (elementaryAbelianPRank_subgroup_le hr.one_lt _) (hrank r))

def outsideSigmaFittingCore (M : Subgroup G) : Subgroup G :=
  (fittingPiPart (sigmaPrimes M)ᶜ ↥M).map M.subtype

theorem outsideSigmaFittingCore_eq_map (M : Subgroup G) :
    outsideSigmaFittingCore M = (fittingPiPart (sigmaPrimes M)ᶜ ↥M).map M.subtype := (rfl)

theorem outsideSigmaFittingCore_le (M : Subgroup G) : outsideSigmaFittingCore M ≤ M := by
  rw [outsideSigmaFittingCore_eq_map]; exact Subgroup.map_subtype_le _

theorem natCard_outsideSigmaFittingCore (M : Subgroup G) :
    Nat.card ↥(outsideSigmaFittingCore M) = Nat.card ↥(fittingPiPart (sigmaPrimes M)ᶜ ↥M) := by
  rw [outsideSigmaFittingCore_eq_map, Subgroup.card_map_of_injective M.subtype_injective]

theorem isPiSubgroup_outsideSigmaFittingCore (M : Subgroup G) :
    IsPiSubgroup (sigmaPrimes M)ᶜ (outsideSigmaFittingCore M) := by
  rw [isPiSubgroup_iff_isPiNumber, natCard_outsideSigmaFittingCore]
  exact isPiSubgroup_iff_isPiNumber.1 (isPiSubgroup_fittingPiPart _ _)

theorem notMem_sigmaPrimes_of_dvd_natCard_outsideSigmaFittingCore (M : Subgroup G) {p : ℕ}
    (hp : p.Prime) (hdvd : p ∣ Nat.card ↥(outsideSigmaFittingCore M)) : p ∉ sigmaPrimes M :=
  isPiSubgroup_iff.1 (isPiSubgroup_outsideSigmaFittingCore M) p
    (Nat.mem_primeFactors.2 ⟨hp, hdvd, Nat.card_pos.ne'⟩)

theorem le_normalizer_outsideSigmaFittingCore (M : Subgroup G) :
    M ≤ normalizer ((outsideSigmaFittingCore M : Subgroup G) : Set G) := by
  rw [outsideSigmaFittingCore_eq_map]
  exact le_normalizer_map_subtype_of_characteristic _ M.le_normalizer

theorem outsideSigmaFittingCore_le_centralizer_sigmaCore (M : Subgroup G) :
    outsideSigmaFittingCore M ≤ centralizer ((sigmaCore M : Subgroup G) : Set G) := by
  have hnorm : ((outsideSigmaFittingCore M).subgroupOf M).Normal :=
    normal_subgroupOf_of_le_normalizer (outsideSigmaFittingCore_le M)
      (le_normalizer_outsideSigmaFittingCore M)
  refine le_centralizer_of_coprime_of_normal_subgroupOf (sigmaCore_le M)
    (outsideSigmaFittingCore_le M) inferInstance hnorm ?_
  exact (isPiSubgroup_iff_isPiNumber.1 (isPiSubgroup_sigmaCore M)).coprime_of_compl
    (isPiSubgroup_iff_isPiNumber.1 (isPiSubgroup_outsideSigmaFittingCore M))
    Nat.card_pos.ne' Nat.card_pos.ne'

theorem isNilpotent_outsideSigmaFittingCore (M : Subgroup G) :
    Group.IsNilpotent ↥(outsideSigmaFittingCore M) := by
  refine isNilpotent_of_le_of_isNilpotent (B := (fittingRaw ↥M).map M.subtype) ?_
    (isNilpotent_map_fittingRaw M)
  rw [outsideSigmaFittingCore_eq_map]
  exact Subgroup.map_mono fittingPiPart_le_fittingRaw

theorem isCyclic_outsideSigmaFittingCore
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₃ : Statements.FTS_proper_subgroup_p_length_one.{u})
    (hG : Prep08.IsMinimalSimpleOddOrder G) {M : Subgroup G} (hM : IsCoatom M) :
    IsCyclic ↥(outsideSigmaFittingCore M) := by
  have hnil := isNilpotent_outsideSigmaFittingCore M
  have hinf : outsideSigmaFittingCore M ⊓ centralizer ((sigmaCore M : Subgroup G) : Set G)
      = outsideSigmaFittingCore M :=
    inf_eq_left.2 (outsideSigmaFittingCore_le_centralizer_sigmaCore M)
  have hrank := FTS_outside_sigma_core_centralizer_rank_one h₁ h₂ h₃ G hG M
    (outsideSigmaFittingCore M) hM (outsideSigmaFittingCore_le M)
    (fun p hp hdvd => notMem_sigmaPrimes_of_dvd_natCard_outsideSigmaFittingCore M hp hdvd)
  refine isCyclic_of_isNilpotent_of_forall_elementaryAbelianPRank_le_one
    (hG.odd_natCard.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)) fun r => ?_
  have h := hrank r
  rwa [hinf] at h

def sigmaFittingPart (M : Subgroup G) : Subgroup G :=
  (fittingPiPart (sigmaPrimes M) ↥M).map M.subtype

theorem sigmaFittingPart_eq_map (M : Subgroup G) :
    sigmaFittingPart M = (fittingPiPart (sigmaPrimes M) ↥M).map M.subtype := (rfl)

theorem sigmaFittingPart_le (M : Subgroup G) : sigmaFittingPart M ≤ M := by
  rw [sigmaFittingPart_eq_map]; exact Subgroup.map_subtype_le _

theorem sigmaFittingPart_le_sigmaCore (M : Subgroup G) : sigmaFittingPart M ≤ sigmaCore M := by
  refine le_sigmaCore (sigmaFittingPart_le M) ?_ ?_
  · rw [sigmaFittingPart_eq_map, subgroupOf_map_subtype_self]
    have := characteristic_subgroupOf_fittingPiPart (sigmaPrimes M) ↥M
    infer_instance
  · rw [isPiSubgroup_iff_isPiNumber, sigmaFittingPart_eq_map,
      Subgroup.card_map_of_injective M.subtype_injective]
    exact isPiSubgroup_iff_isPiNumber.1 (isPiSubgroup_fittingPiPart _ _)

theorem sigmaFittingPart_sup_outsideSigmaFittingCore (M : Subgroup G) :
    sigmaFittingPart M ⊔ outsideSigmaFittingCore M = (fittingRaw ↥M).map M.subtype := by
  rw [sigmaFittingPart_eq_map, outsideSigmaFittingCore_eq_map, ← Subgroup.map_sup,
    fittingPiPart_sup_compl]

omit [Finite G] in
theorem commutator_le_centralizer_of_isCyclic {M Z : Subgroup G} [IsCyclic ↥Z]
    (hMZ : M ≤ normalizer (Z : Set G)) :
    (⁅M, M⁆ : Subgroup G) ≤ centralizer (Z : Set G) :=
  Subgroup.commutator_le.2 fun _ hx _ hy =>
    commutatorElement_mem_centralizer_of_isCyclic (hMZ hx) (hMZ hy)

theorem le_map_fittingRaw_of_le_centralizer {M Y : Subgroup G} [Group.IsSolvable ↥M]
    (hYM : Y ≤ M)
    (hY : Y ≤ centralizer (((fittingRaw ↥M).map M.subtype : Subgroup G) : Set G)) :
    Y ≤ (fittingRaw ↥M).map M.subtype := by
  have h1 : Y.subgroupOf M ≤ centralizer
      ((((fittingRaw ↥M).map M.subtype).subgroupOf M : Subgroup ↥M) : Set ↥M) :=
    subgroupOf_le_centralizer_subgroupOf hY
  rw [subgroupOf_map_subtype_self] at h1
  have h2 : Y.subgroupOf M ≤ fittingRaw ↥M := le_fittingRaw_of_le_centralizer_fittingRaw h1
  have h3 := Subgroup.map_mono (f := M.subtype) h2
  rwa [Subgroup.map_subgroupOf_eq_of_le hYM] at h3

theorem le_outsideSigmaFittingCore {M Y : Subgroup G} (hYM : Y ≤ M)
    (hYF : Y ≤ (fittingRaw ↥M).map M.subtype)
    (hYpi : IsPiSubgroup (sigmaPrimes M)ᶜ Y) : Y ≤ outsideSigmaFittingCore M := by
  have h1 : Y.subgroupOf M ≤ fittingRaw ↥M := by
    have h := Subgroup.comap_mono (f := M.subtype) hYF
    rwa [← Subgroup.subgroupOf, ← Subgroup.subgroupOf, subgroupOf_map_subtype_self] at h
  have hpi : IsPiSubgroup (sigmaPrimes M)ᶜ (Y.subgroupOf M) := by
    rw [isPiSubgroup_iff_isPiNumber, natCard_subgroupOf_of_le hYM]
    exact isPiSubgroup_iff_isPiNumber.1 hYpi
  have h2 := le_fittingPiPart_of_le_fittingRaw h1 hpi
  have h3 := Subgroup.map_mono (f := M.subtype) h2
  rwa [Subgroup.map_subgroupOf_eq_of_le hYM, ← outsideSigmaFittingCore_eq_map] at h3

theorem FTS_outside_sigma_derived_centralizer_cyclic
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₃ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FTS_outside_sigma_derived_centralizer_cyclic.{u} := by
  intro G _ _ hG M K Y hM hKM hK hYdef
  have hsolvM : Group.IsSolvable ↥M := hG.isSolvable_of_ne_top M hM.1
  have hZcyc : IsCyclic ↥(outsideSigmaFittingCore M) :=
    isCyclic_outsideSigmaFittingCore h₁ h₂ h₃ hG hM
  have hMZ := le_normalizer_outsideSigmaFittingCore M
  have hYM' : Y ≤ (⁅M, M⁆ : Subgroup G) := by rw [hYdef]; exact inf_le_right
  have hYZ : Y ≤ centralizer ((outsideSigmaFittingCore M : Subgroup G) : Set G) :=
    hYM'.trans (commutator_le_centralizer_of_isCyclic hMZ)
  have hYS : Y ≤ centralizer ((sigmaCore M : Subgroup G) : Set G) := by
    rw [hYdef]; exact le_trans inf_le_left inf_le_right
  have hYFs : Y ≤ centralizer ((sigmaFittingPart M : Subgroup G) : Set G) :=
    hYS.trans (Subgroup.centralizer_le (by exact_mod_cast sigmaFittingPart_le_sigmaCore M))
  have hYF : Y ≤ centralizer (((fittingRaw ↥M).map M.subtype : Subgroup G) : Set G) := by
    rw [← sigmaFittingPart_sup_outsideSigmaFittingCore M]
    exact le_centralizer_sup hYFs hYZ
  have hYK : Y ≤ K := by rw [hYdef]; exact le_trans inf_le_left inf_le_left
  have hYM : Y ≤ M := hYM'.trans (Subgroup.commutator_le_self M)
  have hYFit : Y ≤ (fittingRaw ↥M).map M.subtype := le_map_fittingRaw_of_le_centralizer hYM hYF
  have hYpi : IsPiSubgroup (sigmaPrimes M)ᶜ Y := by
    refine isPiSubgroup_iff.2 fun p hp => ?_
    rw [Nat.mem_primeFactors] at hp
    exact hK p hp.1 (hp.2.1.trans (Subgroup.card_dvd_of_le hYK))
  have hYZle : Y ≤ outsideSigmaFittingCore M := le_outsideSigmaFittingCore hYM hYFit hYpi
  exact ⟨Subgroup.isCyclic_of_le hYZle, le_normalizer_of_le_of_isCyclic hYZle hMZ⟩

end

end CFSG.FeitThompson.Proofs
