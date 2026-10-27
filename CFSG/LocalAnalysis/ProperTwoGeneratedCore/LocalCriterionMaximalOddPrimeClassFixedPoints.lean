module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeFixedSets

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalOddPrimeClass

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

variable {G : Type*} [Group G]

theorem restricted_native_fixed_iff_original
    (H Y : Subgroup G) (Delta : Set (pointRightCosetSpace H))
    (hstable : ∀ y ∈ Y, ∀ omega ∈ Delta,
      pointRightCosetMul H omega y ∈ Delta)
    (A : Subgroup Y) (omega : Delta) :
    letI := pointInvariantSetInverseRightAction H Y Delta hstable
    omega ∈ MulAction.fixedPoints A Delta ↔
      omega.val ∈ pointFixedSet H (A.map Y.subtype) := by
  let := pointInvariantSetInverseRightAction H Y Delta hstable
  constructor
  · intro hfixed g hg
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
    have hf := congrArg Subtype.val (hfixed (⟨a⁻¹, A.inv_mem ha⟩ : A))
    change pointRightCosetMul H omega.val ((a⁻¹ : Y) : G)⁻¹ = omega.val at hf
    change pointRightCosetMul H omega.val (a : G) = omega.val
    simpa only [Subgroup.coe_inv, inv_inv] using hf
  · intro hfixed a
    apply Subtype.ext
    change pointRightCosetMul H omega.val ((a : Y) : G)⁻¹ = omega.val
    exact hfixed _ (Subgroup.mem_map_of_mem Y.subtype (A.inv_mem a.property))

theorem restricted_fixed_set_card_le_original [Finite G]
    (H Y : Subgroup G) (Delta : Set (pointRightCosetSpace H))
    (hstable : ∀ y ∈ Y, ∀ omega ∈ Delta,
      pointRightCosetMul H omega y ∈ Delta) (A : Subgroup Y) :
    letI := pointInvariantSetInverseRightAction H Y Delta hstable
    Nat.card (MulAction.fixedPoints A Delta) ≤
      Nat.card (pointFixedSet H (A.map Y.subtype)) := by
  let := pointInvariantSetInverseRightAction H Y Delta hstable
  let f : MulAction.fixedPoints A Delta → pointFixedSet H (A.map Y.subtype) :=
    fun omega => ⟨omega.val.val,
      (restricted_native_fixed_iff_original H Y Delta hstable A omega.val).mp omega.property⟩
  apply Nat.card_le_card_of_injective f
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun omega : pointFixedSet H (A.map Y.subtype) => omega.val) hab

end CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalOddPrimeClass
