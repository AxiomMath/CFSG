module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullAlgebra
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.ElementaryHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionIndexTwoLocalHull

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII

variable {G : Type*} [Group G]

theorem conjugate_hull_normal (z u g : G) :
    ((localInvolutionPointHull z (rightConjugateElem u g)).subgroupOf
      (Subgroup.centralizer ({rightConjugateElem u g} : Set G))).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer
    (local_point_hull_normalized_by_centralizer z (rightConjugateElem u g))

theorem distinguished_mem_conjugate_hull {z u g t : G}
    (ht : t ∈ involutionPointClass z) (htv : Commute t (rightConjugateElem u g)) :
    t ∈ localInvolutionPointHull z (rightConjugateElem u g) :=
  mem_localInvolutionPointHull ht htv

theorem conjugate_hull_involutions_in_point_class (z u g : G)
    (hI : ∀ x ∈ localInvolutionPointHull z u, orderOf x = 2 →
      x ∈ involutionPointClass z) :
    ∀ y ∈ localInvolutionPointHull z (rightConjugateElem u g), orderOf y = 2 →
      y ∈ involutionPointClass z := by
  intro y hy hyorder
  let E := localHullConjugateEquiv z u g
  let Y : localInvolutionPointHull z (rightConjugateElem u g) := ⟨y, hy⟩
  let X := E.symm Y
  have hXorder : orderOf (X : G) = 2 := by
    calc
      orderOf (X : G) = orderOf X := Subgroup.orderOf_coe X
      _ = orderOf Y := E.symm.orderOf_eq Y
      _ = orderOf y := (Subgroup.orderOf_coe Y).symm
      _ = 2 := hyorder
  have hXclass := hI X X.property hXorder
  have hyconj : rightConjugateElem (X : G) g = y := by
    have hh := congrArg
      (fun x : localInvolutionPointHull z (rightConjugateElem u g) => (x : G))
      (E.apply_symm_apply Y)
    change (localHullConjugateEquiv z u g X : G) = y at hh
    rw [localHullConjugateEquiv_apply] at hh
    exact hh
  rw [← hyconj]
  exact pointClass_right_conjugate_mem hXclass g

theorem conjugate_hull_oddCore_map (z u g : G) :
    (oddCore (localInvolutionPointHull z u)).map
        (localHullConjugateEquiv z u g).toMonoidHom =
      oddCore (localInvolutionPointHull z (rightConjugateElem u g)) := by
  rw [oddCore_eq_twoPrimeCore, oddCore_eq_twoPrimeCore]
  exact CFSG.pPrimeCore_map_iso 2 (localHullConjugateEquiv z u g)

theorem conjugate_hull_oddCore_eq_bot (z u g : G)
    (hodd : oddCore (localInvolutionPointHull z u) = ⊥) :
    oddCore (localInvolutionPointHull z (rightConjugateElem u g)) = ⊥ := by
  rw [← conjugate_hull_oddCore_map, hodd, Subgroup.map_bot]

theorem conjugate_hull_ambient_oddCore_map (z u g : G) :
    ((oddCore (localInvolutionPointHull z u)).map
        (localInvolutionPointHull z u).subtype).map (MulAut.conj g⁻¹).toMonoidHom =
      (oddCore (localInvolutionPointHull z (rightConjugateElem u g))).map
        (localInvolutionPointHull z (rightConjugateElem u g)).subtype := by
  have he : (localInvolutionPointHull z (rightConjugateElem u g)).subtype.comp
      (localHullConjugateEquiv z u g).toMonoidHom =
        (MulAut.conj g⁻¹).toMonoidHom.comp (localInvolutionPointHull z u).subtype := by
    ext x
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
      localHullConjugateEquiv_apply, MulAut.conj_apply, inv_inv]
  rw [Subgroup.map_map, ← he, ← Subgroup.map_map, conjugate_hull_oddCore_map]

end CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull
