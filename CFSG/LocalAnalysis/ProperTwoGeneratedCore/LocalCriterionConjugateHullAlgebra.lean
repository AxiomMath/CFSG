module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometryZStar

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII

variable {G : Type*} [Group G]

theorem point_class_conjugate_image (z g : G) :
    (MulAut.conj g⁻¹) '' involutionPointClass z = involutionPointClass z := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    simpa only [MulAut.conj_apply, inv_inv, rightConjugateElem] using
      pointClass_right_conjugate_mem hs g
  · intro ht
    refine ⟨rightConjugateElem t g⁻¹, pointClass_right_conjugate_mem ht g⁻¹, ?_⟩
    simp only [MulAut.conj_apply, rightConjugateElem, inv_inv, mul_assoc,
      inv_mul_cancel_left, inv_mul_cancel, mul_one]

theorem centralizer_map_mulEquiv {K : Type*} [Group K] (e : G ≃* K) (u : G) :
    (Subgroup.centralizer ({u} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e u} : Set K) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    simpa only [MulEquiv.coe_toMonoidHom, map_mul] using
      congrArg e (Subgroup.mem_centralizer_singleton_iff.mp hy)
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      Subgroup.mem_centralizer_singleton_iff.mp hx

theorem centralizer_conjugate_map (u g : G) :
    (Subgroup.centralizer ({u} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom =
      Subgroup.centralizer ({rightConjugateElem u g} : Set G) := by
  simpa only [MulAut.conj_apply, inv_inv, rightConjugateElem] using
    centralizer_map_mulEquiv (MulAut.conj g⁻¹) u

theorem local_hull_generators_conjugate_image (z u g : G) :
    (MulAut.conj g⁻¹) ''
        (involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G)) =
      involutionPointClass z ∩
        (Subgroup.centralizer ({rightConjugateElem u g} : Set G) : Set G) := by
  rw [Set.image_inter (MulAut.conj g⁻¹).injective, point_class_conjugate_image]
  congr 1
  exact congrArg (fun A : Subgroup G => (A : Set G)) (centralizer_conjugate_map u g)

theorem local_hull_conjugate_map (z u g : G) :
    (localInvolutionPointHull z u).map (MulAut.conj g⁻¹).toMonoidHom =
      localInvolutionPointHull z (rightConjugateElem u g) := by
  rw [localInvolutionPointHull, MonoidHom.map_closure, MulEquiv.coe_toMonoidHom,
    local_hull_generators_conjugate_image]
  rfl

@[expose] def localHullConjugateEquiv (z u g : G) :
    localInvolutionPointHull z u ≃*
      localInvolutionPointHull z (rightConjugateElem u g) where
  toFun x := ⟨g⁻¹ * x.val * g, by
    rw [← local_hull_conjugate_map]
    exact Subgroup.mem_map.mpr ⟨x.val, x.property, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩⟩
  invFun y := ⟨g * y.val * g⁻¹, by
    have hy : y.val ∈ (localInvolutionPointHull z u).map
        (MulAut.conj g⁻¹).toMonoidHom := by
      rw [local_hull_conjugate_map]
      exact y.property
    obtain ⟨x, hx, heq⟩ := Subgroup.mem_map.mp hy
    have heq' : g⁻¹ * x * g = y.val := by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using heq
    have hback : g * y.val * g⁻¹ = x := by rw [← heq']; group
    exact hback.symm ▸ hx⟩
  left_inv x := Subtype.ext (by dsimp; group)
  right_inv x := Subtype.ext (by dsimp; group)
  map_mul' x y := Subtype.ext (by dsimp; group)

theorem localHullConjugateEquiv_apply (z u g : G)
    (x : localInvolutionPointHull z u) :
    (localHullConjugateEquiv z u g x : G) = g⁻¹ * x.val * g := by
  rfl

theorem localHullConjugateEquiv_symm_apply (z u g : G)
    (x : localInvolutionPointHull z (rightConjugateElem u g)) :
    ((localHullConjugateEquiv z u g).symm x : G) = g * x.val * g⁻¹ := by
  rfl

end CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull
