module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldProjection
public import Mathlib.FieldTheory.Finite.GaloisField

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField

universe u v

open scoped MatrixGroups IsMulCommutative

variable {F : Type u} [Field F]

theorem elementary_subgroup (p : ℕ) {G : Type v} [Group G]
    [CFSG.IsElementaryAbelian p G] (B : Subgroup G) :
    CFSG.IsElementaryAbelian p B := by
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
  intro b
  apply Subtype.ext
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (CFSG.IsElementaryAbelian.exponent_dvd_p p G) b.val

theorem elementary_comap_injective (p : ℕ) {G : Type u} {H : Type v}
    [Group G] [Group H] (A : Subgroup G) [CFSG.IsElementaryAbelian p A]
    (f : H →* G) (hf : Function.Injective f) :
    CFSG.IsElementaryAbelian p (A.comap f) := by
  refine
    { toIsMulCommutative := A.comap_injective_isMulCommutative hf
      exponent_dvd_p := ?_ }
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
  intro b
  apply Subtype.ext
  apply hf
  have hp : (⟨f b.val, b.property⟩ : A) ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (CFSG.IsElementaryAbelian.exponent_dvd_p p A) _
  simpa only [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one, Subtype.coe_mk]
    using congrArg Subtype.val hp

instance linearIntersectionElementary (A : Subgroup (Gamma F))
    [CFSG.IsElementaryAbelian 2 A] : CFSG.IsElementaryAbelian 2 (linearIntersection A) :=
  elementary_subgroup 2 (linearIntersection A)

instance intersectionSElementary (A : Subgroup (Gamma F))
    [CFSG.IsElementaryAbelian 2 A] : CFSG.IsElementaryAbelian 2 (intersectionS A) :=
  elementary_comap_injective 2 A _ SemidirectProduct.inl_injective

theorem elementary_card_eq_pow_finrank {G : Type u} [Group G] [Finite G]
    [CFSG.IsElementaryAbelian 2 G] :
    Nat.card G = 2 ^ Module.finrank (ZMod 2) (Additive G) := by
  calc
    Nat.card G = Nat.card (Additive G) := Nat.card_congr Additive.ofMul
    _ = 2 ^ Module.finrank (ZMod 2) (Additive G) :=
      (FiniteField.pow_finrank_eq_natCard 2 (Additive G)).symm

theorem elementary_finrank_le_of_card_le {G : Type u} [Group G] [Finite G]
    [CFSG.IsElementaryAbelian 2 G] {r : ℕ} (hcard : Nat.card G ≤ 2 ^ r) :
    Module.finrank (ZMod 2) (Additive G) ≤ r := by
  rw [elementary_card_eq_pow_finrank] at hcard
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcard

end CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
