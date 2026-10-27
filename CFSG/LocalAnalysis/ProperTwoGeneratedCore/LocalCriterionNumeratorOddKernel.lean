module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorCentralizerHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullTripleReduction

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree

universe u

variable {G : Type u} [Group G] [Finite G]

theorem original_local_hull_entire_oddCore_le_centralizer_oddCore
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (u : G) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H) :
    properOddCore (localInvolutionPointHull z u) ≤
      properOddCore (Subgroup.centralizer ({u} : Set G)) := by
  let L := localInvolutionPointHull z u
  let Y := Subgroup.centralizer ({u} : Set G)
  have hLY : L ≤ Y := localInvolutionPointHull_le_centralizer z u
  let : (L.subgroupOf Y).Normal :=
    (original_centralizer_hull_normal_rank_and_embedding h u hu huz hescape).2.1
  rintro x ⟨k, hk, rfl⟩
  have hkY : Subgroup.inclusion hLY k ∈ CFSG.oddCore Y :=
    (CFSG.ComponentClassification.OddCore.normal_step_mem_iff hLY k).mp hk
  exact ⟨Subgroup.inclusion hLY k, hkY, rfl⟩

theorem original_local_hull_entire_oddCore_central_of_commutator
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (u : G) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hcommutator :
      ⁅properOddCore (Subgroup.centralizer ({u} : Set G)), localInvolutionPointHull z u⁆ = ⊥) :
    CFSG.oddCore (localInvolutionPointHull z u) ≤
      Subgroup.center (localInvolutionPointHull z u) := by
  let L := localInvolutionPointHull z u
  let Y := Subgroup.centralizer ({u} : Set G)
  have hcontain := original_local_hull_entire_oddCore_le_centralizer_oddCore
    h u hu huz hescape
  have hcentral : properOddCore Y ≤ Subgroup.centralizer (L : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutator
  intro k hk
  apply Subgroup.mem_center_iff.mpr
  intro l
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp
    (hcentral (hcontain (Subgroup.mem_map_of_mem L.subtype hk))) l l.property

theorem original_centralizer_rank_two_retained_odd_cores_of_triple
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (htriple : distinguishedTripleCentralization H z)
    (u : G) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u)) :
    let L := localInvolutionPointHull z u
    let Y := Subgroup.centralizer ({u} : Set G)
    let R := properOddCore Y
    R ≤ H ∧ ⁅R, L⁆ = ⊥ ∧ properOddCore L ≤ R ∧
      CFSG.oddCore L ≤ Subgroup.center L ∧
      Odd (Nat.card (CFSG.oddCore L)) ∧ CFSG.oddCore L ≤ H.subgroupOf L := by
  let L := localInvolutionPointHull z u
  let Y := Subgroup.centralizer ({u} : Set G)
  have hY : Y < ⊤ := original_involution_centralizer_proper h u hu
  have hzY : z ∈ Y := Subgroup.mem_centralizer_singleton_iff.mpr huz.symm
  have hL : properHull Y z = L :=
    original_centralizer_properHull_eq h.local_datum u hu huz hescape
  have hrankL : 2 ≤ twoRank (properHull Y z) := hL.symm ▸ hrank
  have hRH := properHull_rank_two_entire_oddCore_le_point h hY hzY hescape hrankL
  have hcommutator : ⁅properOddCore Y, L⁆ = ⊥ := by
    rw [← hL]
    exact properHull_rank_two_entire_oddCore_commutator_of_triple
      h htriple hY hzY hescape hrankL
  have hcontain := original_local_hull_entire_oddCore_le_centralizer_oddCore
    h u hu huz hescape
  have hcentral := original_local_hull_entire_oddCore_central_of_commutator
    h u hu huz hescape hcommutator
  have hodd : Odd (Nat.card (CFSG.oddCore L)) :=
    CFSG.ComponentClassification.OddCore.odd_card L
  refine ⟨hRH, hcommutator, hcontain, hcentral, hodd, ?_⟩
  intro k hk
  exact hRH (hcontain (Subgroup.mem_map_of_mem L.subtype hk))

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
