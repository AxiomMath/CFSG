module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingProduct

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem commute_of_mem_sup_of_commute_factors {G : Type*} [Group G] {Y₁ Y₂ : Subgroup G}
    (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a) {c : G} (h₁ : ∀ a ∈ Y₁, c * a = a * c)
    (h₂ : ∀ b ∈ Y₂, c * b = b * c) {z : G} (hz : z ∈ Y₁ ⊔ Y₂) : c * z = z * c := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_eq_of_mem_sup_of_commute hcomm hz
  calc c * (a * b) = (c * a) * b := by group
    _ = (a * c) * b := by rw [h₁ a ha]
    _ = a * (c * b) := by group
    _ = a * (b * c) := by rw [h₂ b hb]
    _ = a * b * c := by group

end CFSG.SeitzReduction.RankOne
