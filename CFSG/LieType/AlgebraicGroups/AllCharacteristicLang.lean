module

public import CFSG.LieType.AlgebraicGroups.FrobeniusDiagram

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley WithConv

theorem exceptional_all_characteristic_field_Lang_surjectivity
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [IsAlgClosed L] [CharP L p] (e : ℕ) (he : 1 ≤ e) :
    (∀ τ : Tag, ∃ S : MulAut (adjointGroup τ L),
      (∀ g, (S g : ModGL τ L) = Units.map (entrywiseHom (iterateFrobenius L p e)) g) ∧
        ∀ x : adjointGroup τ L, ∃ h : adjointGroup τ L, x = h⁻¹ * S h) ∧
    ∀ (t : TwistTag) (j : ℤ), ∃ S : MulAut (adjointGroup t.tag L),
      (∀ g, (S g : ModGL t.tag L) = diagramMap t L ^ j *
        Units.map (entrywiseHom (iterateFrobenius L p e)) g * (diagramMap t L ^ j)⁻¹) ∧
        ∀ x : adjointGroup t.tag L, ∃ h : adjointGroup t.tag L, x = h⁻¹ * S h := by
  refine ⟨fun τ => ⟨frobTwistAut p e 1 (map_conj_one_adjointGroup τ L), fun g => ?_,
    exists_eq_inv_mul_frobTwistAut p he 1 _⟩, fun t j =>
    ⟨frobTwistAut p e _ (map_conj_diagramMap_zpow t L j), fun g => rfl,
      exists_eq_inv_mul_frobTwistAut p he _ _⟩⟩
  rw [coe_frobTwistAut, frobTwistGL_apply, one_mul, inv_one, mul_one]

end CFSG.LieType.AlgebraicGroups
