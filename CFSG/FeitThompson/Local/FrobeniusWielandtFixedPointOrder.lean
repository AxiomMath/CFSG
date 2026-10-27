module

public import Mathlib.Algebra.BigOperators.Fin
public import CFSG.FeitThompson.Local.WielandtFixedPointOrderSolvable
import CFSG.FeitThompson.Local.ConjugateFixedPointOrders
import CFSG.FeitThompson.Local.FrobeniusGroupIndicatorRelation

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise

variable {A K : Type*} [Group A] [Group K] {U W : Subgroup A}

theorem natCard_fixedPoints_bot (ρ : A →* MulAut K) :
    Nat.card {v : K // ∀ b ∈ (⊥ : Subgroup A), ρ b v = v} = Nat.card K :=
  Nat.card_congr (Equiv.subtypeUnivEquiv fun v b hb => by
    rw [Subgroup.mem_bot] at hb; simp [hb])

theorem natCard_fixedPoints_top (ρ : A →* MulAut K) :
    Nat.card {v : K // ∀ b ∈ (⊤ : Subgroup A), ρ b v = v}
      = Nat.card (FixedPoints.subgroup ρ.range K) := by
  rw [← natCard_fixedPoints_comp_subtype_eq_natCard_subtype, MonoidHom.range_comp,
    Subgroup.range_subtype, ← MonoidHom.range_eq_map]

theorem natCard_fixedPoints_conj_smul (ρ : A →* MulAut K) (a : A) (B : Subgroup A) :
    Nat.card {v : K // ∀ b ∈ (MulAut.conj a • B : Subgroup A), ρ b v = v}
      = Nat.card {v : K // ∀ b ∈ B, ρ b v = v} := by
  let _ : MulDistribMulAction A K := MulDistribMulAction.compHom K ρ
  have key : ∀ C : Subgroup A,
      Nat.card {v : K // ∀ b ∈ C, ρ b v = v} = Nat.card (FixedPoints.subgroup (↥C) K) := by
    intro C
    rw [← natCard_fixedPoints_comp_subtype_eq_natCard_subtype]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun v =>
      (mem_fixedPoints_comp_subtype_iff ρ C).trans (mem_fixedPoints_subgroup_iff C v).symm)
  have hconj : (MulAut.conj a • B : Subgroup A) = B.map (MulAut.conj a).toMonoidHom := by
    rw [Subgroup.pointwise_smul_def]
    rfl
  rw [key, key, hconj]
  exact card_fixedPoints_subgroup_map_conj a B

section Main

variable [Finite A] [Finite K] [Group.IsSolvable A] [Group.IsSolvable K]

theorem natCard_mul_natCard_fixedPoints_pow_natCard_eq (ρ : A →* MulAut K)
    (hcop : (Nat.card A).Coprime (Nat.card K)) (hU : U.Normal)
    (hUW : Subgroup.IsComplement' U W)
    (hC : ∀ w ∈ W, w ≠ 1 → U ⊓ Subgroup.centralizer {w} = ⊥) :
    Nat.card K * Nat.card {v : K // ∀ b ∈ (⊤ : Subgroup A), ρ b v = v} ^ Nat.card W
      = Nat.card {v : K // ∀ b ∈ U, ρ b v = v}
        * Nat.card {v : K // ∀ b ∈ W, ρ b v = v} ^ Nat.card W := by
  classical
  have _instU := Fintype.ofFinite U
  have hmn : ∀ a : A, ∑ i with a ∈ (Sum.elim ![(⊥ : Subgroup A), ⊤, U]
        (fun u : U => MulAut.conj (u : A)⁻¹ • W) i),
        (Sum.elim ![Nat.card U, 1, 0] (fun _ => 0) : Fin 3 ⊕ U → ℕ) i
      = ∑ i with a ∈ (Sum.elim ![(⊥ : Subgroup A), ⊤, U]
          (fun u : U => MulAut.conj (u : A)⁻¹ • W) i),
        (Sum.elim ![0, 0, 1] (fun _ => 1) : Fin 3 ⊕ U → ℕ) i := by
    intro a
    have key := natCard_mul_indicator_one_add_one hU hUW hC a
    rw [finsum_eq_sum_of_fintype] at key
    simp only [Set.indicator_apply, Pi.one_apply, Set.mem_singleton_iff, SetLike.mem_coe,
      mul_ite, mul_one, mul_zero] at key
    simp only [Finset.sum_filter, Fintype.sum_sum_type, Fin.sum_univ_three,
      Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, Subgroup.mem_bot, Subgroup.mem_top, if_true, ite_self,
      add_zero, zero_add]
    simpa using key
  have key := prod_natCard_centralizer_pow_eq ρ hcop _ _ _ hmn
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type] at key
  simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
    natCard_fixedPoints_bot, natCard_fixedPoints_conj_smul, Subgroup.card_bot, Subgroup.card_top,
    one_mul, mul_one, zero_mul, pow_zero, Finset.prod_const_one] at key
  have hconjcard : ∀ u : U, Nat.card (MulAut.conj (u : A)⁻¹ • W : Subgroup A) = Nat.card W :=
    fun u => Nat.card_congr (Subgroup.equivSMul _ _).symm.toEquiv
  rw [Finset.prod_congr rfl (fun u _ => by rw [hconjcard u]), Finset.prod_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card, ← pow_mul, ← hUW.card_mul_card,
    mul_comm (Nat.card U) (Nat.card W)] at key
  refine Nat.pow_left_injective (n := Nat.card U) Nat.card_pos.ne' ?_
  simpa [natCard_fixedPoints_top, mul_pow, ← pow_mul] using key

theorem natCard_mul_natCard_fixedPoints_range_pow_natCard_eq (ρ : A →* MulAut K)
    (hcop : (Nat.card A).Coprime (Nat.card K)) (hU : U.Normal)
    (hUW : Subgroup.IsComplement' U W)
    (hC : ∀ w ∈ W, w ≠ 1 → U ⊓ Subgroup.centralizer {w} = ⊥) :
    Nat.card K * Nat.card (FixedPoints.subgroup ρ.range K) ^ Nat.card W
      = Nat.card (FixedPoints.subgroup (ρ.comp U.subtype).range K)
        * Nat.card (FixedPoints.subgroup (ρ.comp W.subtype).range K) ^ Nat.card W := by
  rw [← natCard_fixedPoints_top, natCard_fixedPoints_comp_subtype_eq_natCard_subtype,
    natCard_fixedPoints_comp_subtype_eq_natCard_subtype]
  exact natCard_mul_natCard_fixedPoints_pow_natCard_eq ρ hcop hU hUW hC

end Main

end CFSG.FeitThompson
