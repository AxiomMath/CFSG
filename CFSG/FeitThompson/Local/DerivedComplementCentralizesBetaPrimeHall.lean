module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.BetaPrimeDerivedNilpotent
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.BetaPrimeDerivedComplement
import CFSG.FeitThompson.Foundations.NormalHallIntersectionHall
import CFSG.FeitThompson.Foundations.PiSubgroupInHallSolvable
import CFSG.FeitThompson.Local.PrimeCentralizerTransitiveHyperplanes
import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
import CFSG.FeitThompson.Local.BetaPrimesSigmaCompatibility
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

open CFSG.FeitThompson Subgroup

universe u

variable {G : Type u} [Group G]

theorem isHallPiSubgroupOf_inf_of_normal [Finite G] {π σ : Set ℕ} {S K W : Subgroup G}
    (hSW : S ≤ W) (hKW : K ≤ W) (hSnorm : (S.subgroupOf W).Normal)
    (hSσ : IsPiSubgroup σ S)
    (hSHall : ∀ r ∈ (S.relIndex W).primeFactors, r ∉ σ)
    (hKπ : IsPiSubgroup π K)
    (hKHall : ∀ r ∈ (K.relIndex W).primeFactors, r ∉ π) :
    CFSG.FeitThompson.IsHallPiSubgroupOf π (K ⊓ S) S := by
  refine ⟨inf_le_right, ?_, ?_⟩
  ·
    refine isPiSubgroup_iff.2 fun r hr => ?_
    rw [natCard_inf_subgroupOf] at hr
    exact isPiSubgroup_iff.1 hKπ r
      (Nat.primeFactors_mono (Subgroup.card_dvd_of_le inf_le_left) Nat.card_pos.ne' hr)
  · intro r hr hrπ
    rw [index_inf_subgroupOf] at hr
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hrdvd : r ∣ K.relIndex S := Nat.dvd_of_mem_primeFactors hr
    have hrσ : r ∈ σ := isPiSubgroup_iff.1 hSσ r
      (Nat.mem_primeFactors.2 ⟨hrp, hrdvd.trans (Subgroup.relIndex_dvd_card K S),
        Nat.card_pos.ne'⟩)
    have hH1 : (K ⊓ S).relIndex S = K.relIndex S := Subgroup.inf_relIndex_right K S
    have hH2 : (K ⊓ S).relIndex K = S.relIndex K := Subgroup.inf_relIndex_left K S
    have hm1 := Subgroup.relIndex_mul_relIndex (K ⊓ S) S W inf_le_right hSW
    have hm2 := Subgroup.relIndex_mul_relIndex (K ⊓ S) K W inf_le_left hKW
    have hdvdW : r ∣ (K ⊓ S).relIndex W := by
      rw [← hm1]
      exact Dvd.dvd.mul_right (hH1 ▸ hrdvd) _
    rw [← hm2, hH2] at hdvdW
    rcases (Nat.Prime.dvd_mul hrp).1 hdvdW with h | h
    · exact hSHall r (Nat.mem_primeFactors.2 ⟨hrp,
        h.trans (relIndex_dvd_relIndex_of_normal hKW hSnorm),
        Subgroup.index_ne_zero_of_finite (H := S.subgroupOf W)⟩) hrσ
    · exact hKHall r (Nat.mem_primeFactors.2 ⟨hrp, h,
        Subgroup.index_ne_zero_of_finite (H := K.subgroupOf W)⟩) hrπ

theorem FTS_derived_complement_centralizes_beta_prime_hall
    (h₁ : CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FTS_derived_complement_centralizes_beta_prime_hall.{u} := by
  intro G _ _ hG M hM E hEM hsd
  have hMc : IsCoatom M := hM
  have : Fintype G := Fintype.ofFinite G
  have hsimple := hG.isSimpleGroup
  have hG2 : CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hG6 : Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  obtain ⟨hHallOf, hHallG, hSM'⟩ := h₁ G hG2 M hMc
  set π : Set ℕ := {r : ℕ | r.Prime ∧ r ∉ betaPrimes ↥M} with hπ
  have hβσ : betaPrimes ↥M ⊆ sigmaPrimes M :=
    betaPrimes_subset_sigmaPrimes hG.not_isMulCommutative hG.odd_natCard hG.isSolvable hMc
  have hEσ : ∀ r ∈ (Nat.card ↥E).primeFactors, r ∉ sigmaPrimes M := by
    rw [← index_subgroupOf_left_eq hsd]
    exact hHallOf.2.notMem_of_mem_primeFactors_index
  have hE'E : (⁅E, E⁆ : Subgroup G) ≤ E := Subgroup.commutator_le_self E
  have hE'M' : (⁅E, E⁆ : Subgroup G) ≤ (⁅M, M⁆ : Subgroup G) := Subgroup.commutator_mono hEM hEM
  have hM'M : (⁅M, M⁆ : Subgroup G) ≤ M := Subgroup.commutator_le_self M
  have hsolvM' : Group.IsSolvable ↥(⁅M, M⁆ : Subgroup G) :=
    isSolvable_of_le_of_isSolvable hM'M (hG.isSolvable M hMc.1)
  have hE'σ : ∀ r ∈ (Nat.card ↥(⁅E, E⁆ : Subgroup G)).primeFactors, r ∉ sigmaPrimes M :=
    fun r hr => hEσ r
      (Nat.primeFactors_mono (Subgroup.card_dvd_of_le hE'E) Nat.card_pos.ne' hr)
  have hE'π : IsPiSubgroup π (⁅E, E⁆ : Subgroup G) :=
    isPiSubgroup_iff.2 fun r hr =>
      ⟨Nat.prime_of_mem_primeFactors hr, fun hrβ => hE'σ r hr (hβσ hrβ)⟩
  have hUπ : IsPiSubgroup π ((⁅E, E⁆ : Subgroup G).subgroupOf (⁅M, M⁆ : Subgroup G)) := by
    refine isPiSubgroup_iff.2 fun r hr => isPiSubgroup_iff.1 hE'π r ?_
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'M').toEquiv] at hr
  obtain ⟨K₀, hK₀hall, hUK₀⟩ :=
    @exists_isHallSubgroup_ge_of_isPiSubgroup _ _ π _ hsolvM' _ hUπ
  set K : Subgroup G := K₀.map (⁅M, M⁆ : Subgroup G).subtype with hKdef
  have hKM' : K ≤ (⁅M, M⁆ : Subgroup G) := Subgroup.map_subtype_le _
  have hcardK : Nat.card ↥K = Nat.card ↥K₀ := by
    rw [hKdef, Subgroup.card_map_of_injective (⁅M, M⁆ : Subgroup G).subtype_injective]
  have hKrel : K.relIndex (⁅M, M⁆ : Subgroup G) = K₀.index := relIndex_map_subtype K₀
  have hE'K : (⁅E, E⁆ : Subgroup G) ≤ K := by
    have h := Subgroup.map_mono (f := (⁅M, M⁆ : Subgroup G).subtype) hUK₀
    rwa [Subgroup.map_subgroupOf_eq_of_le hE'M'] at h
  have hKπ : IsPiSubgroup π K := by
    refine isPiSubgroup_iff.2 fun r hr => ?_
    rw [hcardK] at hr
    exact isPiNumber_iff.1 hK₀hall.natCard r hr
  have hKHall : ∀ r ∈ (K.relIndex (⁅M, M⁆ : Subgroup G)).primeFactors, r ∉ π := by
    intro r hr
    rw [hKrel] at hr
    exact isPiNumber_iff.1 hK₀hall.index r hr
  have hnil : Group.IsNilpotent ↥K :=
    FTS_beta_prime_derived_nilpotent h₁ h₂ G hG6 M hMc K hKM'
      fun r hr => (isPiSubgroup_iff.1 hKπ r hr).2
  have hSnorm : ((sigmaCore M).subgroupOf (⁅M, M⁆ : Subgroup G)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSM').2
      (hM'M.trans (le_normalizer_sigmaCore M))
  have hSHall : ∀ r ∈ ((sigmaCore M).relIndex (⁅M, M⁆ : Subgroup G)).primeFactors,
      r ∉ sigmaPrimes M := by
    intro r hr
    refine hHallOf.2.notMem_of_mem_primeFactors_index r ?_
    rw [index_subgroupOf]
    refine Nat.mem_primeFactors.2 ⟨Nat.prime_of_mem_primeFactors hr,
      (Nat.dvd_of_mem_primeFactors hr).trans
        (relIndex_dvd_relIndex_of_normal hM'M (sigmaCore_normal_subgroupOf M)), ?_⟩
    rw [← index_subgroupOf]
    exact Subgroup.index_ne_zero_of_finite
  refine ⟨K ⊓ sigmaCore M, isHallPiSubgroupOf_inf_of_normal hSM' hKM' hSnorm
    hHallG.isPiSubgroup hSHall hKπ hKHall, ?_⟩
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine le_centralizer_of_coprime_natCard_of_isNilpotent K hnil hE'K inf_le_left ?_
  refine Nat.coprime_of_dvd fun r hr hrE' hrK => ?_
  refine hE'σ r (Nat.mem_primeFactors.2 ⟨hr, hrE', Nat.card_pos.ne'⟩) ?_
  refine isPiSubgroup_iff.1 hHallG.isPiSubgroup r ?_
  exact Nat.mem_primeFactors.2 ⟨hr,
    hrK.trans (Subgroup.card_dvd_of_le inf_le_right), Nat.card_pos.ne'⟩

end

end CFSG.FeitThompson.Proofs
