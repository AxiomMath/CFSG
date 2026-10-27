module

public import CFSG.FeitThompson.OddOrder.GeometricSumCongruences
public import CFSG.FeitThompson.OddOrder.FreeActionKernelCongruence

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Finset MulAction

variable {p q : ℕ} (A U : Type*) [Group A] [Group U] [Finite A] [Finite U]

theorem not_forall_eq_one_of_mul_card_eq_sum_range_pow [MulDistribMulAction A U]
    (hq : 1 < q) (hqp : q < p) (hA : Nat.card A = p)
    (hU : q * Nat.card U = ∑ i ∈ range q, p ^ i) :
    ¬ ∀ k : U, k ≠ 1 → ∀ a : A, a • k = k → a = 1 := by
  intro h
  have hdvd : p ∣ Nat.card U - 1 := by
    rw [← hA]
    exact card_dvd_card_sub_one_of_smul_eq_self A U h
  have hu : Nat.card U ≡ 1 [MOD p] := ((Nat.modEq_iff_dvd' Nat.card_pos).2 hdvd).symm
  have hq1 : q ≡ 1 [MOD p] :=
    calc q = q * 1 := by ring
      _ ≡ q * Nat.card U [MOD p] := (Nat.ModEq.refl q).mul hu.symm
      _ = ∑ i ∈ range q, p ^ i := hU
      _ ≡ 1 [MOD p] := sum_range_pow_modEq_one (by omega)
  have := Nat.le_of_dvd (by omega) ((Nat.modEq_iff_dvd' (by omega)).1 hq1.symm)
  omega

theorem not_forall_stabilizer_eq_bot_of_mul_card_eq_sum_range_pow [MulDistribMulAction A U]
    (hq : 1 < q) (hqp : q < p) (hA : Nat.card A = p)
    (hU : q * Nat.card U = ∑ i ∈ range q, p ^ i) :
    ¬ ∀ k : U, k ≠ 1 → stabilizer A k = ⊥ := by
  intro h
  refine not_forall_eq_one_of_mul_card_eq_sum_range_pow A U hq hqp hA hU fun k hk a ha => ?_
  have hmem : a ∈ stabilizer A k := mem_stabilizer_iff.2 ha
  rw [h k hk] at hmem
  simpa using hmem

theorem not_exists_free_mulAut_hom_of_mul_card_eq_sum_range_pow (hq : 1 < q) (hqp : q < p)
    (hA : Nat.card A = p) (hU : q * Nat.card U = ∑ i ∈ range q, p ^ i) :
    ¬ ∃ φ : A →* MulAut U, ∀ k : U, k ≠ 1 → ∀ a : A, φ a k = k → a = 1 := by
  rintro ⟨φ, hφ⟩
  let inst : MulDistribMulAction A U := MulDistribMulAction.compHom U φ
  exact not_forall_eq_one_of_mul_card_eq_sum_range_pow A U hq hqp hA hU hφ

theorem not_exists_free_mulAut_hom_zmod_of_mul_card_eq_sum_range_pow (hq : 1 < q) (hqp : q < p)
    (hU : q * Nat.card U = ∑ i ∈ range q, p ^ i) :
    ¬ ∃ φ : Multiplicative (ZMod p) →* MulAut U,
      ∀ k : U, k ≠ 1 → ∀ a : Multiplicative (ZMod p), φ a k = k → a = 1 := by
  have : NeZero p := ⟨by omega⟩
  exact not_exists_free_mulAut_hom_of_mul_card_eq_sum_range_pow _ U hq hqp
    (by simp [Nat.card_eq_fintype_card]) hU

end CFSG.FeitThompson
