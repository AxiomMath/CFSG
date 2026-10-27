module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeFixedSets

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree

open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki
open CFSG.Open
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

variable {G : Type*} [Group G]

theorem normalizer_inverse_action_two_pretransitive_original_right
    (H W : Subgroup G)
    (htwo :
      let N := Subgroup.normalizer (W : Set G)
      letI := pointInvariantSetInverseRightAction H N (pointFixedSet H W)
        (fun _ hn _ ha => normalizer_preserves_pointFixedSet hn ha)
      MulAction.IsMultiplyPretransitive N (pointFixedSet H W) 2) :
    ∀ a ∈ pointFixedSet H W, ∀ b ∈ pointFixedSet H W,
      ∀ c ∈ pointFixedSet H W, ∀ d ∈ pointFixedSet H W,
        a ≠ b → c ≠ d → ∃ n ∈ Subgroup.normalizer (W : Set G),
          pointRightCosetMul H a n = c ∧ pointRightCosetMul H b n = d := by
  let N := Subgroup.normalizer (W : Set G)
  let := pointInvariantSetInverseRightAction H N (pointFixedSet H W)
    (fun _ hn _ ha => normalizer_preserves_pointFixedSet hn ha)
  intro a ha b hb c hc d hd hab hcd
  let aF : pointFixedSet H W := ⟨a, ha⟩
  let bF : pointFixedSet H W := ⟨b, hb⟩
  let cF : pointFixedSet H W := ⟨c, hc⟩
  let dF : pointFixedSet H W := ⟨d, hd⟩
  have habF : aF ≠ bF := fun heq => hab (congrArg Subtype.val heq)
  have hcdF : cF ≠ dF := fun heq => hcd (congrArg Subtype.val heq)
  obtain ⟨n, hna, hnb⟩ := (MulAction.is_two_pretransitive_iff.mp htwo) habF hcdF
  refine ⟨(n : G)⁻¹, N.inv_mem n.property, ?_, ?_⟩
  · exact congrArg Subtype.val hna
  · exact congrArg Subtype.val hnb

theorem entire_class_empty_excludes_covered_four_groups
    (z : G) (N : Subgroup G)
    (hempty : (N : Set G) ∩ involutionPointClass z = ∅)
    (hcoverage : ∀ A : Subgroup G, IsElemAbelian 2 A → Nat.card A = 4 →
      ∃ s ∈ A, s ∈ involutionPointClass z) :
    ∀ A : Subgroup G, A ≤ N → IsElemAbelian 2 A → Nat.card A ≠ 4 := by
  intro A hAN hA hcard
  obtain ⟨s, hsA, hsclass⟩ := hcoverage A hA hcard
  have hs : s ∈ (N : Set G) ∩ involutionPointClass z := ⟨hAN hsA, hsclass⟩
  rw [hempty] at hs
  exact hs

end CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
