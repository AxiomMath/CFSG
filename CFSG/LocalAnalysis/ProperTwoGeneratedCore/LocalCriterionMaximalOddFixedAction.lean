module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeFixedSets
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Permutation

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalOddFixed

open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

variable {G : Type*} [Group G]

@[expose, instance_reducible] def pointGroupInverseRightAction (H : Subgroup G) :
    MulAction G (pointRightCosetSpace H) where
  smul g omega := pointRightCosetMul H omega g⁻¹
  one_smul omega := by
    change pointRightCosetMul H omega (1 : G)⁻¹ = omega
    simp only [inv_one, pointRightCosetMul_one]
  mul_smul g k omega := by
    change pointRightCosetMul H omega (g * k)⁻¹ =
      pointRightCosetMul H (pointRightCosetMul H omega k⁻¹) g⁻¹
    simp only [mul_inv_rev, pointRightCosetMul_mul]

theorem pointGroupInverseRightAction_fixed_set (H P : Subgroup G) :
    (letI := pointGroupInverseRightAction H
     fixedPointsOfSubgroup G (pointRightCosetSpace H) P) = pointFixedSet H P := by
  ext omega
  change (∀ g ∈ P, pointRightCosetMul H omega g⁻¹ = omega) ↔ _
  constructor
  · intro hf g hg
    simpa only [inv_inv] using hf g⁻¹ (P.inv_mem hg)
  · intro hf g hg
    exact hf g⁻¹ (P.inv_mem hg)

theorem maximal_three_point_normalizer_two_pretransitive [Finite G]
    (H : Subgroup G)
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (p : ℕ) (hp : p.Prime) (P : Subgroup G) (hP : IsPGroup p P)
    (hthree : 3 ≤ Nat.card (pointFixedSet H P))
    (hmax : ∀ Q : Subgroup G, IsPGroup p Q → P ≤ Q →
      3 ≤ Nat.card (pointFixedSet H Q) → Q ≤ P) :
    let N := Subgroup.normalizer (P : Set G)
    letI := pointInvariantSetInverseRightAction H N (pointFixedSet H P)
      (fun _ hn _ ha => normalizer_preserves_pointFixedSet hn ha)
    MulAction.IsMultiplyPretransitive N (pointFixedSet H P) 2 := by
  let := pointGroupInverseRightAction H
  have htwo : MulAction.IsMultiplyPretransitive G (pointRightCosetSpace H) 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    obtain ⟨g, hga, hgb⟩ := hdoubly a b c d hab hcd
    refine ⟨g⁻¹, ?_, ?_⟩
    · change pointRightCosetMul H a g⁻¹⁻¹ = c
      simpa only [inv_inv] using hga
    · change pointRightCosetMul H b g⁻¹⁻¹ = d
      simpa only [inv_inv] using hgb
  have hsets (Q : Subgroup G) :
      fixedPointsOfSubgroup G (pointRightCosetSpace H) Q = pointFixedSet H Q :=
    pointGroupInverseRightAction_fixed_set H Q
  have hmaxNative : Maximal (fun Q : Subgroup G =>
      IsPGroup p Q ∧ 2 < Nat.card {a : pointRightCosetSpace H //
        a ∈ fixedPointsOfSubgroup G (pointRightCosetSpace H) Q}) P := by
    constructor
    · refine ⟨hP, ?_⟩
      rw [hsets P]
      exact Nat.lt_of_lt_of_le (by decide : 2 < 3) hthree
    · intro Q hQ hPQ
      apply hmax Q hQ.1 hPQ
      have hc := hQ.2
      rw [hsets Q] at hc
      change 2 < Nat.card (pointFixedSet H Q) at hc
      omega
  have hNtwo := chapter1_bender_normalizer_two_pretransitive hp htwo P hmaxNative
  rw [hsets P] at hNtwo
  let N := Subgroup.normalizer (P : Set G)
  let := pointInvariantSetInverseRightAction H N (pointFixedSet H P)
    (fun _ hn _ ha => normalizer_preserves_pointFixedSet hn ha)
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c d hab hcd
  obtain ⟨n, hna, hnb⟩ := hNtwo a.property b.property c.property d.property
    (fun heq => hab (Subtype.ext heq)) (fun heq => hcd (Subtype.ext heq))
  exact ⟨n, Subtype.ext hna, Subtype.ext hnb⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalOddFixed
