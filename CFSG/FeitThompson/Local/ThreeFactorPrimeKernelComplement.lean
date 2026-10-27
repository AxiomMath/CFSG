module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.PGroup
import CFSG.FeitThompson.Foundations.ProductSubgroupsCardinality

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise Subgroup

variable {E : Type*} [Group E]

private theorem natCard_sup_of_coe_mul_of_inf_eq_bot {H K : Subgroup E}
    (hmul : (↑(H ⊔ K) : Set E) = (H : Set E) * (K : Set E)) (hinf : H ⊓ K = ⊥) :
    Nat.card (H ⊔ K : Subgroup E) = Nat.card H * Nat.card K := by
  have h := natCard_mul_mul_natCard_inf H K
  rw [hinf, Subgroup.card_bot, mul_one, ← hmul] at h
  simpa using h

structure IsThreeFactorPrimeKernelSetup (p : ℕ) {E : Type*} [Group E] [Finite E]
    (E3 P E1 A0 P0 : Subgroup E) : Prop where
  prime : p.Prime
  normal_E3 : E3.Normal
  isComplement_E3 : E3.IsComplement' (P ⊔ E1)
  E1_le_normalizer_P : E1 ≤ normalizer (P : Set E)
  inf_P_E1 : P ⊓ E1 = ⊥
  isPGroup_P : IsPGroup p P
  not_dvd_card_E3 : ¬ p ∣ Nat.card E3
  not_dvd_card_E1 : ¬ p ∣ Nat.card E1
  normal_A0 : A0.Normal
  card_A0 : Nat.card A0 = p
  A0_le_P : A0 ≤ P
  P0_le_P : P0 ≤ P
  E1_le_normalizer_P0 : E1 ≤ normalizer (P0 : Set E)
  sup_A0_P0 : A0 ⊔ P0 = P
  inf_A0_P0 : A0 ⊓ P0 = ⊥

namespace IsThreeFactorPrimeKernelSetup

variable {p : ℕ} {E3 P E1 A0 P0 : Subgroup E} [Finite E]
  (hd : IsThreeFactorPrimeKernelSetup p E3 P E1 A0 P0)

include hd

theorem coe_sup_P0_E1 : (↑(P0 ⊔ E1) : Set E) = (P0 : Set E) * (E1 : Set E) :=
  Subgroup.coe_mul_of_right_le_normalizer_left P0 E1 hd.E1_le_normalizer_P0

theorem coe_sup_eq_mul :
    (↑(E3 ⊔ (P0 ⊔ E1)) : Set E) = (E3 : Set E) * ((P0 : Set E) * (E1 : Set E)) := by
  have := hd.normal_E3
  rw [Subgroup.normal_mul, hd.coe_sup_P0_E1]

theorem inf_P0_E1 : P0 ⊓ E1 = ⊥ :=
  le_bot_iff.1 (hd.inf_P_E1 ▸ inf_le_inf_right E1 hd.P0_le_P)

theorem inf_E3_sup_P0_E1 : E3 ⊓ (P0 ⊔ E1) = ⊥ := by
  refine le_bot_iff.1 ?_
  have h := hd.isComplement_E3.isCompl.inf_eq_bot
  exact h ▸ inf_le_inf_left E3 (sup_le_sup_right hd.P0_le_P E1)

theorem card_sup_P0_E1 : Nat.card (P0 ⊔ E1 : Subgroup E) = Nat.card P0 * Nat.card E1 :=
  natCard_sup_of_coe_mul_of_inf_eq_bot hd.coe_sup_P0_E1 hd.inf_P0_E1

theorem card_sup :
    Nat.card (E3 ⊔ (P0 ⊔ E1) : Subgroup E) = Nat.card E3 * (Nat.card P0 * Nat.card E1) := by
  have := hd.normal_E3
  rw [natCard_sup_of_coe_mul_of_inf_eq_bot (Subgroup.normal_mul E3 (P0 ⊔ E1)) hd.inf_E3_sup_P0_E1,
    hd.card_sup_P0_E1]

theorem card_P : Nat.card P = p * Nat.card P0 := by
  have := hd.normal_A0
  rw [← hd.sup_A0_P0,
    natCard_sup_of_coe_mul_of_inf_eq_bot (Subgroup.normal_mul A0 P0) hd.inf_A0_P0, hd.card_A0]

theorem card_eq : Nat.card E = Nat.card E3 * (Nat.card P * Nat.card E1) := by
  have h1 : Nat.card E3 * Nat.card (P ⊔ E1 : Subgroup E) = Nat.card E := by
    simpa using hd.isComplement_E3.card_mul_card
  have h2 : Nat.card (P ⊔ E1 : Subgroup E) = Nat.card P * Nat.card E1 :=
    natCard_sup_of_coe_mul_of_inf_eq_bot
      (Subgroup.coe_mul_of_right_le_normalizer_left P E1 hd.E1_le_normalizer_P) hd.inf_P_E1
  rw [← h1, h2]

theorem sup_A0_sup : A0 ⊔ (E3 ⊔ (P0 ⊔ E1)) = ⊤ := by
  have h : A0 ⊔ (E3 ⊔ (P0 ⊔ E1)) = E3 ⊔ ((A0 ⊔ P0) ⊔ E1) := by ac_rfl
  rw [h, hd.sup_A0_P0]
  exact hd.isComplement_E3.isCompl.sup_eq_top

theorem card_A0_mul_card_sup :
    Nat.card A0 * Nat.card (E3 ⊔ (P0 ⊔ E1) : Subgroup E) = Nat.card E := by
  rw [hd.card_sup, hd.card_A0, hd.card_eq, hd.card_P]
  ring

theorem inf_A0_sup : A0 ⊓ (E3 ⊔ (P0 ⊔ E1) : Subgroup E) = ⊥ := by
  have := hd.normal_A0
  have h := natCard_mul_mul_natCard_inf A0 (E3 ⊔ (P0 ⊔ E1))
  rw [← Subgroup.normal_mul A0 (E3 ⊔ (P0 ⊔ E1)), hd.sup_A0_sup, Subgroup.coe_top,
    Nat.card_univ, ← hd.card_A0_mul_card_sup] at h
  have hpos : 0 < Nat.card A0 * Nat.card (E3 ⊔ (P0 ⊔ E1) : Subgroup E) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  refine Subgroup.card_eq_one.1 (Nat.eq_of_mul_eq_mul_left hpos ?_)
  rw [h, mul_one]

theorem isComplement'_A0 : A0.IsComplement' (E3 ⊔ (P0 ⊔ E1)) := by
  have := hd.normal_A0
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.2 hd.inf_A0_sup) ?_
  rw [← Subgroup.normal_mul A0 (E3 ⊔ (P0 ⊔ E1)), hd.sup_A0_sup, Subgroup.coe_top]

theorem ordProj_card_sup :
    ordProj[p] (Nat.card (E3 ⊔ (P0 ⊔ E1) : Subgroup E)) = Nat.card P0 := by
  have : Fact p.Prime := ⟨hd.prime⟩
  obtain ⟨n, hn⟩ := (hd.isPGroup_P.to_le hd.P0_le_P).exists_card_eq
  rw [hd.card_sup, hn]
  have h3 : Nat.card E3 ≠ 0 := Nat.card_pos.ne'
  have h1 : Nat.card E1 ≠ 0 := Nat.card_pos.ne'
  have hpn : (p : ℕ) ^ n ≠ 0 := pow_ne_zero _ hd.prime.pos.ne'
  rw [Nat.factorization_mul h3 (mul_ne_zero hpn h1), Nat.factorization_mul hpn h1]
  simp [Nat.factorization_eq_zero_of_not_dvd hd.not_dvd_card_E3,
    Nat.factorization_eq_zero_of_not_dvd hd.not_dvd_card_E1,
    Nat.Prime.factorization_pow hd.prime]

omit hd in
theorem P0_le_sup : P0 ≤ E3 ⊔ (P0 ⊔ E1) := le_sup_right.trans' le_sup_left

end IsThreeFactorPrimeKernelSetup

end CFSG.FeitThompson
