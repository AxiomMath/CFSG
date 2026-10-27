module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattiniVector

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini

open CFSG LocalCriterionFourGroupCommutator
open scoped IsMulCommutative

universe u v

variable {A : Type u} [Group A] {V : Type v} [Group V]
variable {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V] [MulDistribMulAction A V]

@[expose] def elementaryCommonFixedSubspace : Submodule (ZMod p) (Additive V) :=
  ⨅ a : A, elementaryActorFixedSubspace (V := V) (p := p) a

theorem elementaryCommonFixedSubspace_mem (x : Additive V) :
    x ∈ elementaryCommonFixedSubspace (A := A) (V := V) (p := p) ↔
      ∀ a : A, a • x.toMul = x.toMul := by
  exact (Submodule.mem_iInf _).trans
    (forall_congr' fun a => elementaryActorFixedSubspace_mem a x)

@[expose] def elementaryCommonFixedSubspaceEquiv :
    let : IsElementaryAbelian p (fixedPointSubgroup A V) :=
      elementary_subgroup (fixedPointSubgroup A V)
    Additive (fixedPointSubgroup A V) ≃ₗ[ZMod p]
      elementaryCommonFixedSubspace (A := A) (V := V) (p := p) := by
  let : IsElementaryAbelian p (fixedPointSubgroup A V) :=
    elementary_subgroup (fixedPointSubgroup A V)
  let e : Additive (fixedPointSubgroup A V) ≃+
      elementaryCommonFixedSubspace (A := A) (V := V) (p := p) :=
    { toFun := fun x => ⟨Additive.ofMul (x.toMul : V),
        elementaryCommonFixedSubspace_mem _ |>.mpr x.toMul.property⟩
      invFun := fun x => Additive.ofMul ⟨x.val.toMul,
        elementaryCommonFixedSubspace_mem _ |>.mp x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  exact LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap p) e.bijective

theorem elementaryCommonFixedSubspace_finrank :
    let : IsElementaryAbelian p (fixedPointSubgroup A V) :=
      elementary_subgroup (fixedPointSubgroup A V)
    Module.finrank (ZMod p) (Additive (fixedPointSubgroup A V)) =
      Module.finrank (ZMod p)
        (elementaryCommonFixedSubspace (A := A) (V := V) (p := p)) := by
  let : IsElementaryAbelian p (fixedPointSubgroup A V) :=
    elementary_subgroup (fixedPointSubgroup A V)
  exact (elementaryCommonFixedSubspaceEquiv (A := A) (V := V) (p := p)).finrank_eq

theorem elementary_common_fixed_card_eq_pow_subspace_finrank [Finite V] :
    Nat.card (fixedPointSubgroup A V) =
      p ^ Module.finrank (ZMod p)
        (elementaryCommonFixedSubspace (A := A) (V := V) (p := p)) := by
  let : IsElementaryAbelian p (fixedPointSubgroup A V) :=
    elementary_subgroup (fixedPointSubgroup A V)
  rw [elementary_card_eq_pow_finrank (p := p), elementaryCommonFixedSubspace_finrank]

theorem elementary_fixed_card_eq_pow_subspace_finrank [Finite V] (a : A) :
    Nat.card (actorFixedSubgroup (I := V) a) =
      p ^ Module.finrank (ZMod p) (elementaryActorFixedSubspace (V := V) (p := p) a) := by
  let : IsElementaryAbelian p (actorFixedSubgroup (I := V) a) :=
    elementary_subgroup (actorFixedSubgroup (I := V) a)
  rw [elementary_card_eq_pow_finrank (p := p), elementaryActorFixedSubspace_finrank]

theorem klein_four_exact_fixed_space_dimension_identity [Finite A] [IsKleinFour A]
    [Finite V] (hpodd : Odd p) (a b : A) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b) :
    Module.finrank (ZMod p) (Additive V) +
        2 * Module.finrank (ZMod p)
          (elementaryCommonFixedSubspace (A := A) (V := V) (p := p)) =
      Module.finrank (ZMod p) (elementaryActorFixedSubspace (V := V) (p := p) a) +
        Module.finrank (ZMod p) (elementaryActorFixedSubspace (V := V) (p := p) b) +
          Module.finrank (ZMod p)
            (elementaryActorFixedSubspace (V := V) (p := p) (a * b)) := by
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup p V).exists_card_eq
  have hodd : Odd (Nat.card V) := by rw [hn]; exact hpodd.pow
  have hidentity := four_group_order_identity a b ha hb hab hodd
  rw [elementary_card_eq_pow_finrank (p := p),
    elementary_common_fixed_card_eq_pow_subspace_finrank (p := p),
    elementary_fixed_card_eq_pow_subspace_finrank (p := p) a,
    elementary_fixed_card_eq_pow_subspace_finrank (p := p) b,
    elementary_fixed_card_eq_pow_subspace_finrank (p := p) (a * b)] at hidentity
  apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
  simpa only [pow_add, pow_mul, Nat.mul_comm 2] using hidentity

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini
