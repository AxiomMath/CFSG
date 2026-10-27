module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.QuadraticActions

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

@[expose] noncomputable def zmodLinearAutomorphisms (prime : ℕ) (G : Type u) [CommGroup G]
    [Module (ZMod prime) (Additive G)] :
    MulAut G →* (Additive G ≃ₗ[ZMod prime] Additive G) where
  toFun equivalence := (MulEquiv.toAdditive equivalence).toLinearEquiv
    (fun scalar member => ZMod.map_smul (MulEquiv.toAdditive equivalence) scalar member)
  map_one' := by
    ext member
    rfl
  map_mul' first second := by
    ext member
    rfl

theorem zmodLinearAutomorphisms_apply (prime : ℕ) (G : Type u) [CommGroup G]
    [Module (ZMod prime) (Additive G)]
    (equivalence : MulAut G) (member : Additive G) :
    zmodLinearAutomorphisms prime G equivalence member =
      Additive.ofMul (equivalence (Additive.toMul member)) := rfl

theorem zmodLinearAutomorphisms_injective (prime : ℕ) (G : Type u) [CommGroup G]
    [Module (ZMod prime) (Additive G)] :
    Function.Injective (zmodLinearAutomorphisms prime G) := by
  intro first second heq
  apply MulEquiv.ext
  intro member
  have happly := DFunLike.congr_fun heq (Additive.ofMul member)
  exact congrArg Additive.toMul happly

@[expose] def LinearPrimeStableAction {actor : Type u} {field : Type v} {space : Type*}
    [Group actor] [Field field] [AddCommGroup space] [Module field space]
    (prime : ℕ) (action : actor →* (space ≃ₗ[field] space)) : Prop :=
  ∀ member : actor, ((action member : Module.End field space) - LinearMap.id) ^ 2 = 0 →
    member ∈ (pCore prime (actor ⧸ action.ker)).comap (QuotientGroup.mk' action.ker)

theorem quadratic_zmod_linear_action (prime : ℕ) (G : Type u) [CommGroup G]
    [Module (ZMod prime) (Additive G)]
    (equivalence : MulAut G) (hquadratic : QuadraticAutomorphism equivalence) :
    ((zmodLinearAutomorphisms prime G equivalence : Module.End (ZMod prime) (Additive G)) -
      LinearMap.id) ^ 2 = 0 := by
  apply LinearMap.ext
  intro member
  rw [pow_two, Module.End.mul_apply]
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.zero_apply]
  apply sub_eq_zero.mpr
  change Additive.ofMul (equivalence (Additive.toMul
      (zmodLinearAutomorphisms prime G equivalence member - member))) =
    zmodLinearAutomorphisms prime G equivalence member - member
  have hdifference : Additive.toMul (zmodLinearAutomorphisms prime G equivalence member - member) =
      (Additive.toMul member)⁻¹ * equivalence (Additive.toMul member) := by
    rw [sub_eq_add_neg]
    change equivalence (Additive.toMul member) * (Additive.toMul member)⁻¹ = _
    exact mul_comm _ _
  rw [hdifference, hquadratic]
  exact congrArg Additive.ofMul hdifference.symm

end CFSG.RankThreeEvenClassification.Helpers
