module

public import Mathlib.GroupTheory.Perm.Fin

public section

namespace CFSG.LinearGroups

open Equiv

theorem regular_permutation_sign {G : Type*} [Group G] [Fintype G] [DecidableEq G] (g : G) :
    1 ≤ orderOf g ∧ orderOf g ∣ Fintype.card G ∧
      Perm.sign (Equiv.mulLeft g) = (-1) ^ (Fintype.card G - Fintype.card G / orderOf g) := by
  classical
  refine ⟨orderOf_pos g, orderOf_dvd_card, ?_⟩
  set C := Subgroup.zpowers g with hC
  let g' : C := ⟨g, Subgroup.mem_zpowers g⟩
  have key : ∀ m : ℕ, 0 < m → g ^ m = 1 → ∀ i : Fin m,
      g ^ ((finRotate m i : Fin m) : ℕ) = g * g ^ (i : ℕ) := by
    intro m hm hgm i
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [finRotate_apply, Fin.val_add_one]
    split_ifs with hi
    · rw [hi, Fin.val_last, pow_zero, ← pow_succ', hgm]
    · rw [pow_succ']
  have hC1 : Perm.sign (Equiv.mulLeft g') = (-1) ^ (orderOf g - 1) := by
    have hx : IsOfFinOrder g := isOfFinOrder_of_finite g
    rw [← sign_finRotate]
    refine (Perm.sign_eq_sign_of_equiv _ _ (finEquivZPowers hx) fun i => ?_).symm
    apply Subtype.ext
    simp only [finEquivZPowers_apply, Equiv.coe_mulLeft, Subgroup.coe_mul]
    exact key _ (orderOf_pos g) (pow_orderOf_eq_one g) i
  let mk : G → Quotient (QuotientGroup.rightRel C) := Quotient.mk (QuotientGroup.rightRel C)
  have hrep : ∀ x : G, x * (Quotient.out (mk x))⁻¹ ∈ C := by
    intro x
    have : QuotientGroup.rightRel C (Quotient.out (mk x)) x := Quotient.exact (Quotient.out_eq _)
    rwa [QuotientGroup.rightRel_apply] at this
  have hmk : ∀ (c : G), c ∈ C → ∀ x : G, mk (c * x) = mk x := by
    intro c hc x
    apply Quotient.sound
    change QuotientGroup.rightRel C (c * x) x
    rw [QuotientGroup.rightRel_apply, mul_inv_rev, mul_inv_cancel_left]
    exact C.inv_mem hc
  let e : G ≃ C × Quotient (QuotientGroup.rightRel C) :=
    { toFun := fun x => (⟨x * (Quotient.out (mk x))⁻¹, hrep x⟩, mk x)
      invFun := fun ct => (ct.1 : G) * Quotient.out ct.2
      left_inv := fun x => by simp
      right_inv := fun ct => by
        obtain ⟨c, q⟩ := ct
        have hq : mk ((c : G) * Quotient.out q) = q := by
          rw [hmk c c.2]
          exact Quotient.out_eq q
        ext
        · simp only [hq, mul_inv_cancel_right]
        · exact hq }
  have hsign : Perm.sign (Equiv.mulLeft g) =
      Perm.sign (Equiv.prodCongrLeft fun _ : Quotient (QuotientGroup.rightRel C) =>
        Equiv.mulLeft g') := by
    refine Perm.sign_eq_sign_of_equiv _ _ e fun x => ?_
    rw [Equiv.prodCongrLeft_apply]
    change ((⟨g * x * (Quotient.out (mk (g * x)))⁻¹, hrep (g * x)⟩ : C), mk (g * x)) =
      (g' * ⟨x * (Quotient.out (mk x))⁻¹, hrep x⟩, mk x)
    have h1 := hmk g (Subgroup.mem_zpowers g) x
    ext
    · simp only [h1, Subgroup.coe_mul, mul_assoc]
      rfl
    · exact h1
  have hT : Fintype.card (Quotient (QuotientGroup.rightRel C)) =
      Fintype.card G / orderOf g := by
    have h1 := Subgroup.card_mul_index C
    rw [Nat.card_zpowers, Nat.card_eq_fintype_card] at h1
    rw [← h1, Nat.mul_div_cancel_left _ (orderOf_pos g), Subgroup.index,
      ← Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel C),
      Nat.card_eq_fintype_card]
  rw [hsign, Perm.sign_prodCongrLeft, Finset.prod_const, Finset.card_univ, hT, hC1, ← pow_mul]
  congr 1
  have hdvd : orderOf g ∣ Fintype.card G := orderOf_dvd_card
  obtain ⟨t, ht⟩ := hdvd
  rw [ht, Nat.mul_div_cancel_left _ (orderOf_pos g), Nat.sub_one_mul]

end CFSG.LinearGroups
