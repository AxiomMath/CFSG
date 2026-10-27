module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeFixedSets

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

variable {G : Type*} [Group G] [Finite G]

theorem hull_centralizer_fixes_involution_fixed_set
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (u : G) (L : Subgroup G)
    (hLC : L ≤ Subgroup.centralizer ({u} : Set G))
    (hr : ∃ r ∈ L, r ∈ involutionPointClass z)
    (htrans : ∀ a b : pointRightCosetSpace H,
      pointRightCosetMul H a u = a → pointRightCosetMul H b u = b →
      ∃ l ∈ L, pointRightCosetMul H a l = b) :
    ∀ j ∈ Subgroup.centralizer (L : Set G),
      ∀ a : pointRightCosetSpace H, pointRightCosetMul H a u = a →
        pointRightCosetMul H a j = a := by
  obtain ⟨r, hrL, hrclass⟩ := hr
  obtain ⟨epsilon, hepsilon, _⟩ :=
    class_centralizer_has_pointFixedSet_point h hrclass
      (le_refl (Subgroup.centralizer ({r} : Set G)))
  have huC : u ∈ Subgroup.centralizer ({r} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (hLC hrL)).symm
  have hepsilonu : pointRightCosetMul H epsilon u = epsilon := hepsilon u huC
  intro j hj a ha
  have hjC : j ∈ Subgroup.centralizer ({r} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hrL) hj
  have hepsilonj : pointRightCosetMul H epsilon j = epsilon := hepsilon j hjC
  obtain ⟨l, hl, hlmap⟩ := htrans epsilon a hepsilonu ha
  have hcomm : l * j = j * l := Subgroup.mem_centralizer_iff.mp hj l hl
  rw [← hlmap, pointRightCosetMul_mul, hcomm, ← pointRightCosetMul_mul, hepsilonj]

theorem hull_centralizer_fixes_original_subset
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (Delta : Set (pointRightCosetSpace H)) (u : G) (L : Subgroup G)
    (huDelta : ∀ a ∈ Delta, pointRightCosetMul H a u = a)
    (hLC : L ≤ Subgroup.centralizer ({u} : Set G))
    (hr : ∃ r ∈ L, r ∈ involutionPointClass z)
    (htrans : ∀ a b : pointRightCosetSpace H,
      pointRightCosetMul H a u = a → pointRightCosetMul H b u = b →
      ∃ l ∈ L, pointRightCosetMul H a l = b) :
    ∀ j ∈ Subgroup.centralizer (L : Set G),
      ∀ a ∈ Delta, pointRightCosetMul H a j = a := by
  intro j hj a ha
  exact hull_centralizer_fixes_involution_fixed_set h u L hLC hr htrans
    j hj a (huDelta a ha)

end CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
