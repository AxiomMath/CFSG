module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoSemilinear

public section

namespace CFSG.LinearGroups

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.GorensteinWalter

universe u

theorem linear_two_coordinate_data (K : Type u) [Field K] :
    (∀ x : K, (none : Omega K) ≠ some x) ∧
      (∀ b : K, translation K b none = none ∧
        ∀ x : K, translation K b (some x) = some (x + b)) ∧
      (inversion K none = some 0 ∧ inversion K (some 0) = none ∧
        ∀ x : K, x ≠ 0 → inversion K (some x) = some (-x⁻¹)) ∧
      (∀ s : Kˣ, multiplier K s none = none ∧
        ∀ x : K, multiplier K s (some x) = some ((s : K) * x)) ∧
      (∀ σ : K ≃+* K, fieldExtension K σ none = none ∧
        ∀ x : K, fieldExtension K σ (some x) = some (σ x)) ∧
      coordinateU K = Subgroup.closure (Set.range (translation K)) ∧
      coordinateG K = Subgroup.closure (Set.range (translation K) ∪ {inversion K}) ∧
      coordinateD K = Subgroup.closure
        ((coordinateG K : Set (Equiv.Perm (Omega K))) ∪ Set.range (multiplier K)) ∧
      coordinateE K = Subgroup.closure
        ((coordinateD K : Set (Equiv.Perm (Omega K))) ∪ Set.range (fieldExtension K)) ∧
      (∀ (f g : Equiv.Perm (Omega K)) (x : Omega K), (f * g) x = f (g x)) ∧
      coordinateEquiv K none = Projectivization.mk K ![1, 0] psl2_e0_ne_zero ∧
      (∀ x : K, coordinateEquiv K (some x) =
        Projectivization.mk K ![x, 1] (psl2AffineVector_ne_zero x)) ∧
      Function.Bijective (coordinateEquiv K) :=
  ⟨fun _ => Option.some_ne_none _ ∘ Eq.symm, fun b => ⟨translation_none K b, translation_some K b⟩,
    ⟨inversion_none K, inversion_zero K, inversion_nonzero K⟩,
    fun s => ⟨multiplier_none K s, multiplier_some K s⟩,
    fun σ => ⟨fieldExtension_none K σ, fieldExtension_some K σ⟩, rfl, rfl, rfl, rfl,
    fun _ _ _ => rfl, rfl, fun _ => rfl, (coordinateEquiv K).bijective⟩

end CFSG.LinearGroups
