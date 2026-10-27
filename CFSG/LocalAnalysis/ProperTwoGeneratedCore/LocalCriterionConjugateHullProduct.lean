module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometryZStar

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII

variable {G : Type*} [Group G]

theorem commuting_product_conjugate (u z t l : G)
    (hul : Commute u l) (hzt : rightConjugateElem z l = t) :
    rightConjugateElem (u * z) l = u * t := by
  have hu : rightConjugateElem u l = u := by
    simp only [rightConjugateElem, mul_assoc]
    rw [hul.eq, inv_mul_cancel_left]
  calc
    rightConjugateElem (u * z) l =
        rightConjugateElem u l * rightConjugateElem z l := by
      simpa only [MulAut.conj_apply, inv_inv, rightConjugateElem] using
        (MulAut.conj l⁻¹).map_mul u z
    _ = u * t := by rw [hu, hzt]

theorem commuting_product_in_original_class (L : Subgroup G) (u z t : G)
    (hLC : L ≤ Subgroup.centralizer ({u} : Set G))
    (hzt : ∃ l ∈ L, rightConjugateElem z l = t)
    (huz : u * z ∈ involutionPointClass u) :
    u * t ∈ involutionPointClass u := by
  obtain ⟨l, hl, hlt⟩ := hzt
  have hul : Commute u l := (Subgroup.mem_centralizer_singleton_iff.mp (hLC hl)).symm
  rw [← commuting_product_conjugate u z t l hul hlt]
  exact pointClass_right_conjugate_mem huz l

theorem local_hull_product_in_original_class (u z t : G)
    (hzt : ∃ l ∈ localInvolutionPointHull z u, rightConjugateElem z l = t)
    (huz : u * z ∈ involutionPointClass u) :
    u * t ∈ involutionPointClass u :=
  commuting_product_in_original_class (localInvolutionPointHull z u) u z t
    (localInvolutionPointHull_le_centralizer z u) hzt huz

theorem local_hull_product_conjugator (u z t : G)
    (hzt : ∃ l ∈ localInvolutionPointHull z u, rightConjugateElem z l = t)
    (huz : u * z ∈ involutionPointClass u) :
    ∃ g : G, rightConjugateElem u g = u * t :=
  local_hull_product_in_original_class u z t hzt huz

end CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull
