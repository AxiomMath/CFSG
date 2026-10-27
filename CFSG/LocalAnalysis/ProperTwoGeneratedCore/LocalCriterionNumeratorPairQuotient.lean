module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairPartition

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.FiveTransitive.CharacteristicAutomorphism
open CFSG.BenderSuzuki.PFAppendixIII

universe v

variable {G : Type v} [Group G]

local instance originalHullOddCoreCharacteristic (z u : G) :
    (CFSG.oddCore (localInvolutionPointHull z u)).Characteristic :=
  CFSG.ComponentClassification.OddCore.characteristic _

@[expose] def originalCentralizerHullConjugation (z u : G) :
    Subgroup.centralizer ({u} : Set G) →* MulAut (localInvolutionPointHull z u) :=
  (localInvolutionPointHull z u).normalizerMonoidHom.comp
    (Subgroup.inclusion
      (CFSG.ProperTwoGeneratedCore.local_point_hull_normalized_by_centralizer z u))

@[expose] def originalCentralizerHullQuotientConjugation (z u : G) :
    Subgroup.centralizer ({u} : Set G) →*
      MulAut (localInvolutionPointHull z u ⧸ CFSG.oddCore (localInvolutionPointHull z u)) :=
  (quotient (CFSG.oddCore (localInvolutionPointHull z u))).comp
    (originalCentralizerHullConjugation z u)

theorem originalCentralizerHullConjugation_ker (z u : G) :
    (originalCentralizerHullConjugation z u).ker =
      (Subgroup.centralizer (localInvolutionPointHull z u : Set G)).subgroupOf
        (Subgroup.centralizer ({u} : Set G)) := by
  ext x
  change (localInvolutionPointHull z u).normalizerMonoidHom
      (Subgroup.inclusion
        (CFSG.ProperTwoGeneratedCore.local_point_hull_normalized_by_centralizer z u) x) = 1 ↔
    (x : G) ∈ Subgroup.centralizer (localInvolutionPointHull z u : Set G)
  rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker]
  rfl

theorem originalCentralizerHullConjugation_central_involution (z u : G) :
    let uM : Subgroup.centralizer ({u} : Set G) :=
      ⟨u, Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl u).eq⟩
    originalCentralizerHullConjugation z u uM = 1 ∧
      originalCentralizerHullQuotientConjugation z u uM = 1 := by
  let uM : Subgroup.centralizer ({u} : Set G) :=
    ⟨u, Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl u).eq⟩
  have huK : uM ∈ (originalCentralizerHullConjugation z u).ker := by
    rw [originalCentralizerHullConjugation_ker]
    apply Subgroup.mem_centralizer_iff.mpr
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (localInvolutionPointHull_le_centralizer z u hl)
  refine ⟨huK, ?_⟩
  change quotient (CFSG.oddCore (localInvolutionPointHull z u))
    (originalCentralizerHullConjugation z u uM) = 1
  rw [show originalCentralizerHullConjugation z u uM = 1 from huK, map_one]

theorem originalCentralizerHullQuotientConjugation_hull_element
    (z u : G) (l : localInvolutionPointHull z u) :
    originalCentralizerHullQuotientConjugation z u
        (Subgroup.inclusion (localInvolutionPointHull_le_centralizer z u) l) =
      MulAut.conj (QuotientGroup.mk' (CFSG.oddCore (localInvolutionPointHull z u)) l) := by
  have hl : originalCentralizerHullConjugation z u
      (Subgroup.inclusion (localInvolutionPointHull_le_centralizer z u) l) =
        MulAut.conj l := by
    apply MulEquiv.ext
    intro k
    apply Subtype.ext
    rfl
  change quotient (CFSG.oddCore (localInvolutionPointHull z u))
    (originalCentralizerHullConjugation z u
      (Subgroup.inclusion (localInvolutionPointHull_le_centralizer z u) l)) = _
  rw [hl, characteristic_quotient_conj]

theorem originalCentralizerHullQuotientConjugation_inner_of_two_cosets
    (z u : G) (x : Subgroup.centralizer ({u} : Set G))
    (hcases : (x : G) = u ∨ (x : G) ∈ localInvolutionPointHull z u ∨
      u * (x : G) ∈ localInvolutionPointHull z u) :
    originalCentralizerHullQuotientConjugation z u x ∈
      innerAutomorphismSubgroup
        (localInvolutionPointHull z u ⧸ CFSG.oddCore (localInvolutionPointHull z u)) := by
  let M := Subgroup.centralizer ({u} : Set G)
  let L := localInvolutionPointHull z u
  let f := originalCentralizerHullQuotientConjugation z u
  let uM : M := ⟨u, Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl u).eq⟩
  have huaction : f uM = 1 :=
    (originalCentralizerHullConjugation_central_involution z u).2
  rcases hcases with hxu | hxL | huxL
  · have hxuM : x = uM := Subtype.ext hxu
    rw [hxuM, huaction]
    exact Subgroup.one_mem _
  · let l : L := ⟨x, hxL⟩
    exact ⟨QuotientGroup.mk' (CFSG.oddCore L) l,
      (originalCentralizerHullQuotientConjugation_hull_element z u l).symm⟩
  · let l : L := ⟨u * (x : G), huxL⟩
    have hl : f (uM * x) = MulAut.conj (QuotientGroup.mk' (CFSG.oddCore L) l) :=
      originalCentralizerHullQuotientConjugation_hull_element z u l
    rw [map_mul, huaction, one_mul] at hl
    exact ⟨QuotientGroup.mk' (CFSG.oddCore L) l, hl.symm⟩

variable [Finite G]

theorem originalCentralizerHullQuotientConjugation_ker_of_central_oddCore
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (u : G)
    (hcentral : CFSG.oddCore (localInvolutionPointHull z u) ≤
      Subgroup.center (localInvolutionPointHull z u)) :
    (originalCentralizerHullQuotientConjugation z u).ker =
      (Subgroup.centralizer (localInvolutionPointHull z u : Set G)).subgroupOf
        (Subgroup.centralizer ({u} : Set G)) := by
  have hgen : Subgroup.closure {x : localInvolutionPointHull z u | IsInvolution x} = ⊤ :=
    original_local_hull_involutionCore_eq_top h u
  have hodd : Odd (Nat.card (CFSG.oddCore (localInvolutionPointHull z u))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hquot : (quotient (CFSG.oddCore (localInvolutionPointHull z u))).ker = ⊥ :=
    characteristic_quotient_ker_eq_bot
      (CFSG.oddCore (localInvolutionPointHull z u)) hodd hcentral hgen
  rw [originalCentralizerHullQuotientConjugation, ← MonoidHom.comap_ker,
    hquot, MonoidHom.comap_bot, originalCentralizerHullConjugation_ker]

theorem original_minimal_failure_pair_every_involution_inner
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hpairRank : twoRank (pairPointStabilizer H beta) ≤ 1)
    (u : G) (huD : u ∈ pairPointStabilizer H beta)
    (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u)) :
    ∀ x : Subgroup.centralizer ({u} : Set G), IsInvolution x →
      originalCentralizerHullQuotientConjugation z u x ∈
        innerAutomorphismSubgroup
          (localInvolutionPointHull z u ⧸ CFSG.oddCore (localInvolutionPointHull z u)) := by
  obtain ⟨_huL, hcases, _hpartition, _hdisj⟩ :=
    original_minimal_failure_pair_centralizer_involution_partition
      h beta hbeta hpairRank u huD hu huz hescape hrank
  intro x hx
  have hxG : IsInvolution (x : G) :=
    ⟨fun heq => hx.ne_one (Subtype.ext heq), congrArg Subtype.val hx.sq_eq_one⟩
  exact originalCentralizerHullQuotientConjugation_inner_of_two_cosets z u x
    (hcases x x.property hxG)

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
