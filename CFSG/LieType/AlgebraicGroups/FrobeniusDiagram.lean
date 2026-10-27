module

public import CFSG.LieType.AlgebraicGroups.FrobeniusDiagramRealized
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley WithConv

open scoped CFSG.ConvolutionPoints

theorem map_conj_one_adjointGroup (τ : Tag) (L : Type) [Field L] :
    (adjointGroup τ L).map (MulAut.conj (1 : ModGL τ L)).toMonoidHom = adjointGroup τ L := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa using hh
  · intro hg
    exact ⟨g, hg, by simp⟩

theorem exceptional_Lang_ordinary_Frobenius_diagram_morphisms
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [IsAlgClosed L] [CharP L p] :
    (∀ (τ : Tag) (e : ℕ), 1 ≤ e →
      ∃ σ : realizedCoord τ L →ₐc[L] realizedCoord τ L,
        (∀ φ, (realizedPointEquiv τ L (pointMap σ φ) : ModGL τ L) =
          Units.map (entrywiseHom (iterateFrobenius L p e)) (realizedPointEquiv τ L φ)) ∧
        (∀ D ∈ tangentSpace L (realizedCoord τ L) (Bialgebra.counitAlgHom L _),
          D ∘ₗ (σ : realizedCoord τ L →ₐ[L] realizedCoord τ L).toLinearMap = 0) ∧
        ∃ θ : MulAut (adjointGroup τ L),
          (∀ g, (θ g : ModGL τ L) = Units.map (entrywiseHom (iterateFrobenius L p e)) g) ∧
          ∀ φ, realizedPointEquiv τ L (pointMap σ φ) = θ (realizedPointEquiv τ L φ)) ∧
    ∀ (t : TwistTag) (j : ℤ) (e : ℕ), 1 ≤ e →
      ∃ σ σ' : realizedCoord t.tag L →ₐc[L] realizedCoord t.tag L,
        (∀ φ, (realizedPointEquiv t.tag L (pointMap σ φ) : ModGL t.tag L) =
          diagramMap t L ^ j * Units.map (entrywiseHom (iterateFrobenius L p e))
            (realizedPointEquiv t.tag L φ) * (diagramMap t L ^ j)⁻¹) ∧
        (∀ φ, (realizedPointEquiv t.tag L (pointMap σ' φ) : ModGL t.tag L) =
          Units.map (entrywiseHom (iterateFrobenius L p (e * t.order)))
            (realizedPointEquiv t.tag L φ)) ∧
        (σ : realizedCoord t.tag L →ₐ[L] realizedCoord t.tag L) ^ t.order =
          (σ' : realizedCoord t.tag L →ₐ[L] realizedCoord t.tag L) ∧
        (∀ D ∈ tangentSpace L (realizedCoord t.tag L) (Bialgebra.counitAlgHom L _),
          D ∘ₗ ((σ : realizedCoord t.tag L →ₐ[L] realizedCoord t.tag L) ^ t.order).toLinearMap =
            0) ∧
        ∃ θ : MulAut (adjointGroup t.tag L),
          (∀ g, (θ g : ModGL t.tag L) = diagramMap t L ^ j *
            Units.map (entrywiseHom (iterateFrobenius L p e)) g * (diagramMap t L ^ j)⁻¹) ∧
          ∀ φ, realizedPointEquiv t.tag L (pointMap σ φ) = θ (realizedPointEquiv t.tag L φ) := by
  refine ⟨fun τ e he => ?_, fun t j e he => ?_⟩
  · have h1 := map_conj_one_adjointGroup τ L
    refine ⟨frobTwistCo p e 1 (conj_mem_adjointGroup_of_map_eq h1), fun φ => ?_,
      fun D hD => tangent_comp_frobTwistCo p he 1 _ hD, frobTwistAut p e 1 h1,
      fun g => ?_, fun φ => ?_⟩
    · rw [realizedPointEquiv_pointMap, frobTwistGL_apply, one_mul, inv_one, mul_one]
    · rw [coe_frobTwistAut, frobTwistGL_apply, one_mul, inv_one, mul_one]
    · apply Subtype.ext
      rw [realizedPointEquiv_pointMap, coe_frobTwistAut]
  · have hQ := map_conj_diagramMap_zpow t L j
    have hd : 1 ≤ t.order := by cases t <;> decide
    have h1 := map_conj_one_adjointGroup t.tag L
    have hpow := frobTwistCo_pow p e (conj_mem_adjointGroup_of_map_eq hQ)
      (entrywiseFrobGL_diagramMap_zpow t p e j) (diagramMap_zpow_pow_order t j)
    refine ⟨frobTwistCo p e _ (conj_mem_adjointGroup_of_map_eq hQ),
      frobTwistCo p (e * t.order) 1 (conj_mem_adjointGroup_of_map_eq h1), fun φ => ?_,
      fun φ => ?_, hpow, fun D hD => ?_, frobTwistAut p e _ hQ, fun g => rfl, fun φ => ?_⟩
    · exact realizedPointEquiv_pointMap p e _ _ φ
    · rw [realizedPointEquiv_pointMap, frobTwistGL_apply, one_mul, inv_one, mul_one]
    · rw [hpow]
      exact tangent_comp_frobTwistCo p (le_trans he (Nat.le_mul_of_pos_right e hd)) 1 _ hD
    · apply Subtype.ext
      rw [realizedPointEquiv_pointMap, coe_frobTwistAut]

end CFSG.LieType.AlgebraicGroups
