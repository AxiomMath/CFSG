module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometry
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalEmbeddingDatum

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity

open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {G : Type u} [Group G]

theorem subgroupOf_conjugacy_image (D K : Subgroup G) (hDK : D ≤ K) (v : K) :
    Subtype.val '' conjugacyWithin (D.subgroupOf K) v =
      conjugacyWithin D (v : G) := by
  ext s
  constructor
  · rintro ⟨x, ⟨d, hd⟩, rfl⟩
    refine ⟨⟨((d : K) : G), d.property⟩, ?_⟩
    exact congrArg Subtype.val hd
  · rintro ⟨d, hd⟩
    let dK : K := ⟨d.val, hDK d.property⟩
    let dDK : D.subgroupOf K := ⟨dK, d.property⟩
    let x : K := rightConjugateElem v dK
    refine ⟨x, ⟨dDK, rfl⟩, ?_⟩
    exact hd

theorem ambient_class_outside_pullback (D K : Subgroup G) (s : G) :
    K.subtype ⁻¹' (involutionPointClass s ∩ ((K : Set G) \ (D : Set G))) =
      {v : K | (v : G) ∈ involutionPointClass s ∧ v ∉ D.subgroupOf K} := by
  ext v
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, v.property, h.2⟩⟩

theorem subgroup_conjugacy_mem_ambient_class (K : Subgroup G)
    (u v : K) (hv : v ∈ conjugacyWithin (⊤ : Subgroup K) u) :
    (v : G) ∈ involutionPointClass (u : G) := by
  obtain ⟨g, hg⟩ := hv
  exact ⟨((g : K) : G), congrArg Subtype.val hg⟩

theorem ambient_two_classes_pullback (K : Subgroup G) (u z : G)
    (htwo : ∀ v : G, orderOf v = 2 →
      v ∈ involutionPointClass u ∨ v ∈ involutionPointClass z) :
    ∀ v : K, IsInvolution v →
      (v : G) ∈ involutionPointClass u ∨ (v : G) ∈ involutionPointClass z := by
  intro v hv
  apply htwo
  rw [Subgroup.orderOf_coe]
  exact orderOf_eq_prime hv.sq_eq_one hv.ne_one

end CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity
