module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearCoordinates

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

open Matrix CatalogueBHigherLinearField

universe u

variable {K : Type u} [Field K] {d : ℕ}

@[expose] def similarityPairs (Q : QuadraticForm K (Fin d → K)) :
    Subgroup (coordinateSemilinearGroup d K) where
  carrier := {g | ∃ mu : Kˣ, ∀ v, Q (coordinateSemilinearMap g v) =
    (mu : K) * g.right (Q v)}
  one_mem' := by
    refine ⟨1, fun v => ?_⟩
    rw [coordinateSemilinearMap_one]
    change Q v = (1 : K) * Q v
    exact (one_mul _).symm
  mul_mem' := by
    rintro g h ⟨mu, hmu⟩ ⟨nu, hnu⟩
    refine ⟨mu * Units.map g.right.toMonoidHom nu, fun v => ?_⟩
    rw [coordinateSemilinearMap_mul, hmu, hnu, map_mul]
    change (mu : K) * (g.right (nu : K) * g.right (h.right (Q v))) =
      ((mu : K) * g.right (nu : K)) * g.right (h.right (Q v))
    exact (mul_assoc _ _ _).symm
  inv_mem' := by
    rintro g ⟨mu, hmu⟩
    refine ⟨Units.map g.right.symm.toMonoidHom mu⁻¹, fun v => ?_⟩
    apply g.right.injective
    apply mul_left_cancel₀ (Units.ne_zero mu)
    rw [← hmu, coordinateSemilinearMap_inv, AddEquiv.apply_symm_apply]
    change Q v = (mu : K) *
      g.right (g.right.symm ((↑mu⁻¹ : K)) * g.right.symm (Q v))
    rw [map_mul, g.right.apply_symm_apply, g.right.apply_symm_apply]
    simp

theorem mem_similarityPairs_iff (Q : QuadraticForm K (Fin d → K))
    (g : coordinateSemilinearGroup d K) :
    g ∈ similarityPairs Q ↔ ∃ mu : Kˣ, ∀ v,
      Q (coordinateSemilinearMap g v) = (mu : K) * g.right (Q v) := Iff.rfl

theorem multiplier_unique (Q : QuadraticForm K (Fin d → K))
    (hQ : ∃ v, Q v ≠ 0) (g : coordinateSemilinearGroup d K) (mu nu : Kˣ)
    (hmu : ∀ v, Q (coordinateSemilinearMap g v) = (mu : K) * g.right (Q v))
    (hnu : ∀ v, Q (coordinateSemilinearMap g v) = (nu : K) * g.right (Q v)) :
    mu = nu := by
  obtain ⟨v, hv⟩ := hQ
  apply Units.ext
  apply mul_right_cancel₀ (show g.right (Q v) ≠ 0 from fun h => hv (g.right.map_eq_zero_iff.mp h))
  exact (hmu v).symm.trans (hnu v)

@[expose] def multiplier (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) : Kˣ := Classical.choose g.property

theorem multiplier_spec (Q : QuadraticForm K (Fin d → K)) (g : similarityPairs Q)
    (v : Fin d → K) :
    Q (coordinateSemilinearMap g.val v) =
      (multiplier Q g : K) * g.val.right (Q v) := Classical.choose_spec g.property v

theorem multiplier_one (Q : QuadraticForm K (Fin d → K)) (hQ : ∃ v, Q v ≠ 0) :
    multiplier Q 1 = 1 := by
  apply multiplier_unique Q hQ 1 _ _ (multiplier_spec Q 1)
  intro v
  rw [coordinateSemilinearMap_one]
  change Q v = (1 : K) * Q v
  exact (one_mul _).symm

theorem multiplier_mul (Q : QuadraticForm K (Fin d → K)) (hQ : ∃ v, Q v ≠ 0)
    (g h : similarityPairs Q) :
    multiplier Q (g * h) = multiplier Q g *
      Units.map g.val.right.toMonoidHom (multiplier Q h) := by
  apply multiplier_unique Q hQ (g * h).val _ _ (multiplier_spec Q (g * h))
  intro v
  change Q (coordinateSemilinearMap (g.val * h.val) v) = _
  rw [coordinateSemilinearMap_mul, multiplier_spec, multiplier_spec, map_mul]
  change (multiplier Q g : K) *
      (g.val.right (multiplier Q h : K) * g.val.right (h.val.right (Q v))) =
    ((multiplier Q g : K) * g.val.right (multiplier Q h : K)) *
      g.val.right (h.val.right (Q v))
  exact (mul_assoc _ _ _).symm

theorem multiplier_inv (Q : QuadraticForm K (Fin d → K)) (hQ : ∃ v, Q v ≠ 0)
    (g : similarityPairs Q) :
    multiplier Q g⁻¹ = Units.map g.val.right.symm.toMonoidHom (multiplier Q g)⁻¹ := by
  apply multiplier_unique Q hQ g⁻¹.val _ _ (multiplier_spec Q g⁻¹)
  intro v
  change Q (coordinateSemilinearMap g.val⁻¹ v) =
    g.val.right.symm ((↑(multiplier Q g)⁻¹ : K)) * g.val.right.symm (Q v)
  apply g.val.right.injective
  apply mul_left_cancel₀ (Units.ne_zero (multiplier Q g))
  rw [← multiplier_spec, coordinateSemilinearMap_inv, AddEquiv.apply_symm_apply]
  change Q v = (multiplier Q g : K) *
    g.val.right (g.val.right.symm ((↑(multiplier Q g)⁻¹ : K)) *
      g.val.right.symm (Q v))
  rw [map_mul, g.val.right.apply_symm_apply, g.val.right.apply_symm_apply]
  simp

@[expose] def fieldProjection (Q : QuadraticForm K (Fin d → K)) :
    similarityPairs Q →* (K ≃+* K) :=
  SemidirectProduct.rightHom.comp (similarityPairs Q).subtype

theorem fieldProjection_apply (Q : QuadraticForm K (Fin d → K)) (g : similarityPairs Q) :
    fieldProjection Q g = g.val.right := rfl

@[expose] def linearSimilarityPairs (Q : QuadraticForm K (Fin d → K)) :
    Subgroup (similarityPairs Q) := (fieldProjection Q).ker

theorem mem_linearSimilarityPairs_iff (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) : g ∈ linearSimilarityPairs Q ↔ g.val.right = 1 := Iff.rfl

end CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
