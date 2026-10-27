module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorNativeAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorCentralizerHull

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

universe u

variable {G : Type u} [Group G]

theorem original_centralizer_preserves_full_fixedSet (H : Subgroup G) (u : G) :
    ∀ y ∈ Subgroup.centralizer ({u} : Set G), ∀ a ∈ elementFixedSet H u,
      pointRightCosetMul H a y ∈ elementFixedSet H u := by
  intro y hy a ha
  have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hy
  change pointRightCosetMul H (pointRightCosetMul H a y) u = pointRightCosetMul H a y
  rw [pointRightCosetMul_mul, hcomm, ← pointRightCosetMul_mul, ha]

@[expose, instance_reducible] def originalCentralizerFixedSetAction
    (H : Subgroup G) (u : G) :
    MulAction (Subgroup.centralizer ({u} : Set G)) (elementFixedSet H u) :=
  pointInvariantSetInverseRightAction H (Subgroup.centralizer ({u} : Set G))
    (elementFixedSet H u) (original_centralizer_preserves_full_fixedSet H u)

theorem originalCentralizerFixedSetAction_hull_inclusion (H : Subgroup G) (z u : G) :
    letI := hullFixedSetAction H z u
    letI := originalCentralizerFixedSetAction H u
    ∀ (l : localInvolutionPointHull z u) (a : elementFixedSet H u),
      Subgroup.inclusion (localInvolutionPointHull_le_centralizer z u) l • a = l • a := by
  let := hullFixedSetAction H z u
  let := originalCentralizerFixedSetAction H u
  intro l a
  apply Subtype.ext
  rfl

theorem original_centralizer_two_pretransitive_of_hull (H : Subgroup G) (z u : G)
    (hdouble : letI := hullFixedSetAction H z u
      MulAction.IsMultiplyPretransitive (localInvolutionPointHull z u) (elementFixedSet H u) 2) :
    letI := originalCentralizerFixedSetAction H u
    MulAction.IsMultiplyPretransitive (Subgroup.centralizer ({u} : Set G))
      (elementFixedSet H u) 2 := by
  let := hullFixedSetAction H z u
  let := originalCentralizerFixedSetAction H u
  apply MulAction.is_two_pretransitive_iff.mpr
  intro a b c d hab hcd
  obtain ⟨l, hla, hlb⟩ := MulAction.is_two_pretransitive_iff.mp hdouble hab hcd
  refine ⟨Subgroup.inclusion (localInvolutionPointHull_le_centralizer z u) l, ?_, ?_⟩
  · rw [originalCentralizerFixedSetAction_hull_inclusion]
    exact hla
  · rw [originalCentralizerFixedSetAction_hull_inclusion]
    exact hlb

variable [Finite G]

theorem original_central_sylow_native_centralizer_two_pretransitive
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (u : G) (huH : u ∈ H) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u)) :
    let L := localInvolutionPointHull z u
    let F := L ⧸ CFSG.oddCore L
    letI := originalCentralizerFixedSetAction H u
    MulAction.IsMultiplyPretransitive (Subgroup.centralizer ({u} : Set G))
      (elementFixedSet H u) 2 ∧
      ∃ a i : ℕ, 2 ≤ a ∧ i ∈ ({1, 2, 3} : Set ℕ) ∧
        IsSimpleBenderGroupAtExponent a F ∧
        Nat.card (elementFixedSet H u) = (2 ^ a) ^ i + 1 := by
  let := originalCentralizerFixedSetAction H u
  obtain ⟨_hmodel, _hcore, _hB, _hfull, a, i, ha, hi, hAt,
    _helem, _hUB, _hUset, _hUcard, _hfour, _hindex, hcard, _hident, hdouble⟩ :=
    original_central_sylow_native_fixedSet_model h S hzS hzcenter u huH hu huz hescape hrank
  exact ⟨original_centralizer_two_pretransitive_of_hull H z u hdouble,
    a, i, ha, hi, hAt, hcard⟩

theorem original_minimal_failure_native_centralizer_action
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (u : G) (huH : u ∈ H) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u)) :
    let L := localInvolutionPointHull z u
    let F := L ⧸ CFSG.oddCore L
    letI := originalCentralizerFixedSetAction H u
    Subgroup.centralizer ({u} : Set G) < ⊤ ∧
      MulAction.IsMultiplyPretransitive (Subgroup.centralizer ({u} : Set G))
        (elementFixedSet H u) 2 ∧
      ∃ a i : ℕ, 2 ≤ a ∧ i ∈ ({1, 2, 3} : Set ℕ) ∧
        IsSimpleBenderGroupAtExponent a F ∧
        Nat.card (elementFixedSet H u) = (2 ^ a) ^ i + 1 := by
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  exact ⟨original_involution_centralizer_proper h u hu,
    original_central_sylow_native_centralizer_two_pretransitive
      h.local_datum S hzS hzcenter u huH hu huz hescape hrank⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
